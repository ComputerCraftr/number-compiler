"""Finite source-word scalar weights over issued 2rev10 actions.

Each accepted step retains the exact canonical decimal source SLP and the
exact source-to-target root seam. A source word is interpreted as its integer
value in base ten; this module does not claim symbolic Laurent-valued
accumulators, an all-depth temporal period, or a source-independent future
quotient. The only repeatable composition is a finite sequence of already
issued one-step actions whose roots meet exactly.
The normalized four-port scalar authority refuses a next step when its source
word ends in decimal zero; callers retain the exact fallback at that seam
instead of trimming the zero and changing the source weight.
"""

from __future__ import annotations

from collections.abc import Callable, Generator, Iterator
from contextlib import contextmanager
from dataclasses import dataclass, field
from functools import partial
from typing import TypeAlias

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import SLPArena, SLPNode
from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.resources.ledger import LedgerReservation, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.metric_keys import double_reverse as _double_reverse_keys

from .temporal_alternating_carry import FourPortSLPProjection
from .temporal_hashlife import DoubleReverseTemporalHashlife
from .temporal_hashlife_types import DoubleReversePortAction

_ISSUER = object()
_LEAF_RECORD_UNITS = 6
_JOIN_RECORD_UNITS = 3


@dataclass(frozen=True, slots=True)
class _SpatialAuthority:
    projection: FourPortSLPProjection


@dataclass(frozen=True, slots=True)
class _TemporalAuthority:
    engine: DoubleReverseTemporalHashlife
    action: DoubleReversePortAction


_Authority: TypeAlias = _SpatialAuthority | _TemporalAuthority


@dataclass(frozen=True, slots=True)
class _SourceWordStep:
    source_root: int
    target_root: int
    weight_root: int
    source_node: SLPNode
    target_node: SLPNode
    weight_node: SLPNode
    authority: _Authority
    binding: _SourceWordStepBinding


@dataclass(frozen=True, slots=True)
class _SourceWordStepBinding:
    source_root: int
    target_root: int
    weight_root: int
    source_node: SLPNode
    target_node: SLPNode
    weight_node: SLPNode
    authority: _Authority


@dataclass(frozen=True, slots=True, eq=False)
class _SourceWordPathNode:
    """Persistent chronological path node; composition copies no prior rows."""

    left: _SourceWordPathNode | None
    right: _SourceWordPathNode | None
    step: _SourceWordStep | None
    first: _SourceWordStep
    last: _SourceWordStep
    count: int


@dataclass(frozen=True, slots=True)
class _SourceWordCocycleBinding:
    arena: SLPArena
    path: _SourceWordPathNode
    reservation: LedgerReservation
    first_source_root: int
    first_source_node: SLPNode
    last_target_root: int
    last_target_node: SLPNode
    count: int


def _require_canonical_source(arena: SLPArena, root: int) -> int:
    """Require one full MSF-first decimal word, with neither end zero-padded.

    The source value is the whole word admitted to this finite ``F`` step.
    It is never a cropped suffix; callers that normalize an odd physical
    cursor must keep and authenticate that cursor's separate seed anchor.
    """
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("source-word root is outside its issuing SLP arena")
    width = arena.nodes[root].length
    if (
        width < 2
        or symbol_at(arena, root, 0) == 0
        or symbol_at(arena, root, width - 1) == 0
    ):
        raise ValueError(
            "source-word weight requires a canonical, trailing-zero-free word"
        )
    return width


def _validate_reservation_scope(
    arena: SLPArena,
    reservation: LedgerReservation,
    *,
    engine: DoubleReverseTemporalHashlife | None = None,
) -> None:
    if type(reservation) is not LedgerReservation:
        raise TypeError("source-word issuance requires its caller-owned reservation")
    ledger = reservation.resource_ledger
    try:
        # A zero-cost reservation also rejects an active tracker whose owner
        # was retired independently of the tracker itself.
        reservation.reserve()
    except (RuntimeError, TypeError, ValueError) as error:
        raise ValueError(
            "source-word reservation scope is closed or foreign"
        ) from error
    if isinstance(arena, LedgerSLPArena) and arena.ledger is not ledger:
        raise ValueError("source-word reservation belongs to another SLP ledger")
    if engine is not None and engine.ledger is not ledger:
        raise ValueError("source-word reservation belongs to another temporal owner")


def _target_from_spatial_projection(
    arena: SLPArena, projection: FourPortSLPProjection
) -> int:
    row = projection.action.row(0, 0)
    left = arena.terminal(1) if row.reverse_out else arena.empty_id
    right = arena.terminal(2) if row.forward_out else arena.empty_id
    target = arena.concat_many((left, row.output_in(arena), right))
    if arena.nodes[target].length != (
        projection.action.input_width + row.reverse_out + row.forward_out
    ):
        raise AssertionError("four-port output changed its exact source width")
    if symbol_at(arena, target, 0) == 0:
        raise ValueError("source-word step requires a normalized target boundary")
    return target


def _step_binding_is_current(step: _SourceWordStep) -> bool:
    if type(step) is not _SourceWordStep:
        return False
    binding = step.binding
    if type(binding) is not _SourceWordStepBinding:
        return False
    return (
        type(binding.source_root) is int
        and type(binding.target_root) is int
        and type(binding.weight_root) is int
        and type(binding.source_node) is SLPNode
        and type(binding.target_node) is SLPNode
        and type(binding.weight_node) is SLPNode
        and binding.source_root == step.source_root
        and binding.target_root == step.target_root
        and binding.weight_root == step.weight_root
        and binding.source_node is step.source_node
        and binding.target_node is step.target_node
        and binding.weight_node is step.weight_node
        and binding.authority is step.authority
    )


def _step_record(
    source_root: int,
    target_root: int,
    weight_root: int,
    arena: SLPArena,
    authority: _Authority,
) -> _SourceWordStep:
    step = _SourceWordStep(
        source_root,
        target_root,
        weight_root,
        arena.nodes[source_root],
        arena.nodes[target_root],
        arena.nodes[weight_root],
        authority,
        _SourceWordStepBinding(
            source_root,
            target_root,
            weight_root,
            arena.nodes[source_root],
            arena.nodes[target_root],
            arena.nodes[weight_root],
            authority,
        ),
    )
    return step


@contextmanager
def _retained_record_reservation(
    reservation: LedgerReservation, units: int
) -> Generator[None, None, None]:
    """Charge a persistent issuance before allocating its retained records.

    Successful issuance leaves the charge on the caller-owned reservation for
    its lifetime. Any failure during publication returns only this operation's
    charge, leaving earlier cocycle records untouched.
    """
    reservation.reserve(entries=units, nodes=units)
    try:
        yield
    except BaseException as publication_error:
        try:
            reservation.release(entries=units, nodes=units)
        except BaseException as cleanup_error:
            raise cleanup_error from publication_error
        raise


def _leaf(step: _SourceWordStep) -> _SourceWordPathNode:
    return _SourceWordPathNode(None, None, step, step, step, 1)


def _join(left: _SourceWordPathNode, right: _SourceWordPathNode) -> _SourceWordPathNode:
    return _SourceWordPathNode(
        left,
        right,
        None,
        left.first,
        right.last,
        left.count + right.count,
    )


def _iter_steps(path: _SourceWordPathNode) -> Iterator[_SourceWordStep]:
    """Traverse one immutable concatenation DAG in chronological order."""
    if (
        type(path) is not _SourceWordPathNode
        or type(path.count) is not int
        or path.count <= 0
    ):
        raise ValueError("malformed source-word path root")
    stack = [path]
    visited = 0
    emitted = 0
    maximum_nodes = 2 * path.count - 1
    while stack:
        node = stack.pop()
        if type(node) is not _SourceWordPathNode:
            raise ValueError("malformed source-word path node")
        visited += 1
        if visited > maximum_nodes:
            raise ValueError("source-word path exceeds its sealed length")
        if node.step is not None:
            if (
                type(node.step) is not _SourceWordStep
                or type(node.count) is not int
                or node.left is not None
                or node.right is not None
                or node.count != 1
                or node.first is not node.step
                or node.last is not node.step
            ):
                raise ValueError("malformed source-word path leaf")
            emitted += 1
            if emitted > path.count:
                raise ValueError("source-word path has too many steps")
            yield node.step
            continue
        if (
            type(node.count) is not int
            or type(node.first) is not _SourceWordStep
            or type(node.last) is not _SourceWordStep
            or node.left is None
            or node.right is None
            or type(node.left) is not _SourceWordPathNode
            or type(node.right) is not _SourceWordPathNode
            or type(node.left.count) is not int
            or type(node.right.count) is not int
            or node.count != node.left.count + node.right.count
            or node.first is not node.left.first
            or node.last is not node.right.last
        ):
            raise ValueError("malformed source-word path join")
        stack.append(node.right)
        stack.append(node.left)
    if emitted != path.count:
        raise ValueError("source-word path length changed after issuance")


@dataclass(frozen=True, slots=True, init=False, eq=False)
class ExactSourceWordCocycle:
    """A finite exact path carrying one scalar source-word weight per step."""

    _arena: SLPArena = field(repr=False)
    _path: _SourceWordPathNode = field(repr=False)
    _issuer: object = field(repr=False)
    _reservation: LedgerReservation = field(repr=False)
    _binding: _SourceWordCocycleBinding = field(repr=False)

    def __init__(self) -> None:
        raise TypeError("source-word paths require an existing action issuer")

    @classmethod
    def _issue(
        cls,
        arena: SLPArena,
        path: _SourceWordPathNode,
        reservation: LedgerReservation,
    ) -> ExactSourceWordCocycle:
        _validate_reservation_scope(arena, reservation)
        if type(path) is not _SourceWordPathNode:
            raise TypeError("source-word issuance requires a sealed path node")
        if (
            type(path.first) is not _SourceWordStep
            or type(path.last) is not _SourceWordStep
        ):
            raise ValueError("source-word path is missing its endpoint steps")
        cocycle = object.__new__(cls)
        object.__setattr__(cocycle, "_arena", arena)
        object.__setattr__(cocycle, "_path", path)
        object.__setattr__(cocycle, "_issuer", _ISSUER)
        object.__setattr__(cocycle, "_reservation", reservation)
        object.__setattr__(
            cocycle,
            "_binding",
            _SourceWordCocycleBinding(
                arena,
                path,
                reservation,
                path.first.source_root,
                path.first.source_node,
                path.last.target_root,
                path.last.target_node,
                path.count,
            ),
        )
        return cocycle

    @classmethod
    def from_spatial(
        cls,
        projection: FourPortSLPProjection,
        arena: SLPArena,
        *,
        expected_source_root: int,
        reservation: LedgerReservation,
    ) -> ExactSourceWordCocycle:
        """Issue one finite step from its already folded canonical source.

        ``expected_source_root`` is the exact, trailing-zero-free word passed
        to the four-port fold. The source SLP itself is the scalar weight;
        no second spatial fold or independent digit scan is performed. If a
        prior target ends in zero, this constructor refuses that next step;
        callers must use the exact source fallback without trimming the word.
        """
        if type(projection) is not FourPortSLPProjection:
            raise TypeError("source-word step needs an issued fold and its arena")
        _validate_reservation_scope(arena, reservation)
        weight_root = projection.source_word_weight_in(
            arena, expected_source_root=expected_source_root
        )
        _require_canonical_source(arena, weight_root)
        with _retained_record_reservation(reservation, _LEAF_RECORD_UNITS):
            target_root = _target_from_spatial_projection(arena, projection)
            step = _step_record(
                weight_root,
                target_root,
                weight_root,
                arena,
                _SpatialAuthority(projection),
            )
            return cls._issue(arena, _leaf(step), reservation)

    @classmethod
    def from_issued_temporal_action(
        cls,
        engine: DoubleReverseTemporalHashlife,
        action: DoubleReversePortAction,
        *,
        reservation: LedgerReservation,
    ) -> ExactSourceWordCocycle:
        """Transport one existing exact F action without repowering it."""
        if type(engine) is not DoubleReverseTemporalHashlife:
            raise TypeError("source-word step needs its live temporal owner")
        _validate_reservation_scope(engine.arena, reservation, engine=engine)
        if (
            type(action) is not DoubleReversePortAction
            or type(action.steps) is not int
            or action.steps != 1
        ):
            raise ValueError("source-word generator requires one issued F step")
        engine.validate_action(action)
        arena = engine.arena
        source_root = engine.root_of(action.source)
        target_root = engine.root_of(action.target)
        _require_canonical_source(arena, source_root)
        if symbol_at(arena, target_root, 0) == 0:
            raise ValueError("source-word step requires a normalized target boundary")
        with _retained_record_reservation(reservation, _LEAF_RECORD_UNITS):
            step = _step_record(
                source_root,
                target_root,
                source_root,
                arena,
                _TemporalAuthority(engine, action),
            )
            return cls._issue(arena, _leaf(step), reservation)

    @property
    def source_root(self) -> int:
        self._validate_header(self._arena)
        return self._path.first.source_root

    @property
    def target_root(self) -> int:
        self._validate_header(self._arena)
        return self._path.last.target_root

    @property
    def f_steps(self) -> int:
        self._validate_header(self._arena)
        return self._path.count

    def _validate_header(self, arena: SLPArena) -> None:
        if (
            type(self) is not ExactSourceWordCocycle
            or type(self._binding) is not _SourceWordCocycleBinding
            or type(self._path) is not _SourceWordPathNode
        ):
            raise ValueError("source-word path is stale, foreign, or malformed")
        path = self._path
        binding = self._binding
        if (
            type(path.first) is not _SourceWordStep
            or type(path.last) is not _SourceWordStep
            or type(binding.first_source_node) is not SLPNode
            or type(binding.last_target_node) is not SLPNode
        ):
            raise ValueError("source-word path endpoints are malformed")
        if (
            self._issuer is not _ISSUER
            or arena is not self._arena
            or binding.arena is not self._arena
            or binding.path is not path
            or type(binding.first_source_root) is not int
            or type(binding.last_target_root) is not int
            or type(path.first.source_root) is not int
            or type(path.last.target_root) is not int
            or binding.first_source_root != path.first.source_root
            or binding.first_source_node is not path.first.source_node
            or binding.last_target_root != path.last.target_root
            or binding.last_target_node is not path.last.target_node
            or type(binding.count) is not int
            or type(path.count) is not int
            or binding.count != path.count
            or path.count <= 0
            or binding.reservation is not self._reservation
        ):
            raise ValueError("source-word path is stale, foreign, or malformed")
        _validate_reservation_scope(arena, self._reservation)

    def _validate_step(
        self,
        arena: SLPArena,
        step: _SourceWordStep,
        previous: _SourceWordStep | None,
        ledger: ResourceLedger | None = None,
    ) -> None:
        if not _step_binding_is_current(step):
            raise ValueError("source-word step changed after issuance")
        for root in (step.source_root, step.target_root, step.weight_root):
            if type(root) is not int or not 0 <= root < len(arena.nodes):
                raise ValueError("source-word path contains a stale SLP root")
        if (
            arena.nodes[step.source_root] is not step.source_node
            or arena.nodes[step.target_root] is not step.target_node
            or arena.nodes[step.weight_root] is not step.weight_node
            or step.weight_root != step.source_root
        ):
            raise ValueError("source-word path node binding is stale")
        _require_canonical_source(arena, step.source_root)
        if previous is not None and (
            previous.target_root != step.source_root
            or previous.target_node is not step.source_node
        ):
            raise ValueError("source-word path has no exact node seam")
        authority = step.authority
        if type(authority) is _SpatialAuthority:
            if (
                ledger is not None
                and isinstance(arena, LedgerSLPArena)
                and arena.ledger is not ledger
            ):
                raise ValueError("source-word scratch ledger differs from its arena")
            if (
                authority.projection.source_word_weight_in(
                    arena, expected_source_root=step.source_root
                )
                != step.weight_root
            ):
                raise ValueError("spatial source-word authority changed")
        elif type(authority) is _TemporalAuthority:
            if ledger is not None and authority.engine.ledger is not ledger:
                raise ValueError("source-word scratch ledger differs from its issuer")
            authority.engine.validate_action(authority.action)
            if (
                authority.engine.root_of(authority.action.source) != step.source_root
                or authority.engine.root_of(authority.action.target) != step.target_root
                or authority.action.steps != 1
            ):
                raise ValueError("temporal source-word authority changed")
        else:
            raise ValueError("source-word path has an unknown action issuer")

    def validate(self, arena: SLPArena) -> None:
        """Revalidate every finite source action and exact SLP seam."""
        self._validate_header(arena)
        ledger = self._reservation.resource_ledger
        previous: _SourceWordStep | None = None
        for step in _iter_steps(self._path):
            self._validate_step(arena, step, previous, ledger)
            previous = step

    def then(self, later: ExactSourceWordCocycle) -> ExactSourceWordCocycle:
        """Join two finite paths only at their exact same-arena SLP root."""
        if type(later) is not ExactSourceWordCocycle:
            raise TypeError("source-word composition requires another issued path")
        self._validate_header(self._arena)
        later._validate_header(self._arena)
        if later._reservation is not self._reservation:
            raise ValueError("source-word composition uses a foreign reservation scope")
        left, right = self._path.last, later._path.first
        if (
            left.target_root != right.source_root
            or left.target_node is not right.source_node
        ):
            raise ValueError("source-word composition lacks exact source seam")
        with _retained_record_reservation(self._reservation, _JOIN_RECORD_UNITS):
            return self._issue(
                self._arena,
                _join(self._path, later._path),
                self._reservation,
            )

    def source_increment_mod(
        self,
        arena: SLPArena,
        modulus: int,
    ) -> int:
        """Evaluate summed exact source integers modulo a positive modulus.

        The DAG fold charges pending work and retained node summaries to the
        same caller-owned reservation that holds this cocycle. Temporary
        charges are returned on success, refusal, or cancellation; the issued
        path remains charged until its reservation scope closes.
        """
        self._validate_header(arena)
        if type(modulus) is not int or modulus < 1:
            raise ValueError("source-word modulus must be a positive exact integer")
        reservation = self._reservation
        ledger = reservation.resource_ledger
        _validate_reservation_scope(arena, reservation)
        total = 0
        memo: dict[int, int] = {}
        memo_entries = 0
        operand_reserve = 0
        worklist_reserve = 0
        try:
            modulus_limbs = max(1, (modulus.bit_length() + 63) // 64)
            # Reserve the live modular operands before Python's ``pow``
            # creates any modulus-sized temporaries. Six limb buffers
            # cover the product, power, residue inputs/output, and the
            # binary-power pair currently being composed.
            initial_operand_reserve = 6 * modulus_limbs
            reservation.reserve(
                entries=initial_operand_reserve,
                nodes=initial_operand_reserve,
            )
            operand_reserve = initial_operand_reserve

            def reserve_exponent(exponent_bits: int) -> None:
                nonlocal operand_reserve
                exponent_limbs = max(1, (exponent_bits + 63) // 64)
                required = 6 * modulus_limbs + exponent_limbs
                if required > operand_reserve:
                    extra = required - operand_reserve
                    reservation.reserve(entries=extra, nodes=extra)
                    operand_reserve = required

            previous: _SourceWordStep | None = None
            for step in _iter_steps(self._path):
                self._validate_step(arena, step, previous, ledger)
                previous = step
                root = step.weight_root
                value = memo.get(root)
                if value is None:
                    retained_values = 0
                    folded: dict[int, tuple[int, int]] | None = None

                    def schedule(count: int) -> None:
                        nonlocal worklist_reserve
                        reservation.reserve(entries=count, nodes=count)
                        worklist_reserve += count

                    def pending(_node: SLPNode) -> None:
                        nonlocal worklist_reserve
                        ledger.bump(
                            _double_reverse_keys.DOUBLE_REVERSE_SOURCE_WORD_FOLD_NODE_VISITS
                        )
                        reservation.release(entries=1, nodes=1)
                        worklist_reserve -= 1

                    def reduce(_node_id: int) -> None:
                        nonlocal retained_values
                        reservation.reserve(entries=1, nodes=1)
                        retained_values += 1

                    def concatenate(
                        left: tuple[int, int], right: tuple[int, int]
                    ) -> tuple[int, int]:
                        reserve_exponent(right[0].bit_length())
                        ledger.bump(
                            _double_reverse_keys.DOUBLE_REVERSE_SOURCE_WORD_FOLD_OPERATIONS
                        )
                        ledger.bump(
                            _double_reverse_keys.DOUBLE_REVERSE_SOURCE_WORD_FOLD_OPERAND_BITS,
                            left[0].bit_length()
                            + right[0].bit_length()
                            + left[1].bit_length()
                            + right[1].bit_length()
                            + modulus.bit_length(),
                        )
                        return (
                            left[0] + right[0],
                            (left[1] * pow(10, right[0], modulus) + right[1]) % modulus,
                        )

                    def repeat(
                        value_pair: tuple[int, int], count: int
                    ) -> tuple[int, int]:
                        reserve_exponent(count.bit_length())
                        return binary_power(
                            value_pair,
                            count,
                            identity=(0, 0),
                            compose=concatenate,
                        ).value

                    try:
                        folded = fold_slp_dag(
                            arena,
                            root,
                            empty_value=(0, 0),
                            terminal_value=lambda digit: (1, digit % modulus),
                            concatenate=concatenate,
                            repeat=repeat,
                            on_schedule=schedule,
                            on_pending=pending,
                            on_reduce=reduce,
                        )
                        length, value = folded[root]
                        if length != arena.nodes[root].length:
                            raise AssertionError(
                                "source-word fold lost its exact width"
                            )
                        reservation.reserve(entries=1, nodes=1)
                        memo_entries += 1
                        memo[root] = value
                    finally:
                        fold_cleanups: list[Callable[[], None]] = []
                        if folded is not None:
                            fold_cleanups.append(folded.clear)
                        if retained_values:
                            fold_cleanups.append(
                                partial(
                                    reservation.release,
                                    entries=retained_values,
                                    nodes=retained_values,
                                )
                            )
                        cleanup_all(fold_cleanups)

                ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_SOURCE_WORD_FOLD_OPERATIONS
                )
                ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_SOURCE_WORD_FOLD_OPERAND_BITS,
                    total.bit_length() + value.bit_length() + modulus.bit_length(),
                )
                total = (total + value) % modulus
        finally:
            cleanups: list[Callable[[], None]] = [memo.clear]
            if memo_entries:
                cleanups.append(
                    partial(
                        reservation.release, entries=memo_entries, nodes=memo_entries
                    )
                )
            if worklist_reserve:
                cleanups.append(
                    partial(
                        reservation.release,
                        entries=worklist_reserve,
                        nodes=worklist_reserve,
                    )
                )
            if operand_reserve:
                cleanups.append(
                    partial(
                        reservation.release,
                        entries=operand_reserve,
                        nodes=operand_reserve,
                    )
                )
            cleanup_all(cleanups)
        return total


__all__ = ["ExactSourceWordCocycle"]
