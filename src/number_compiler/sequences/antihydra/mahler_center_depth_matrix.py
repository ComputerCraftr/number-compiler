"""Mahler's source-restricted 100x100 Boolean center transfer.

The generic six-letter matrix is a *conditional local transducer*, not an
indefinitely realized carry program.  Source-rooted finite relations retain
full integer candidate witnesses across their intermediate frames: matching
only the two-digit center is not enough to authenticate a temporal path.

Unlike the 2rev10 stencil, Mahler uses 3D+(D&1), followed by division by
2.  At a fixed LSD pair position s, with D=L+10**s*C+10**(s+2)*U,

  c = (3*L + (D&1)) // 10**s
  h, m = divmod(3*C+c, 100)
  C' = (m//2) + 50*((U+h)&1).

Width births and re-centering are certified using the *full* pointed source;
no 100-state letter alone can move the center to an unknown neighbor.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from itertools import pairwise

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.fields.boolean_transfer import (
    BooleanMatrix,
    BooleanStateSpace,
)
from number_compiler.sequences.antihydra.mahler_center_algebra import (
    STATES,
    center_next,
    conditional_center_moore,
)
from number_compiler.sequences.antihydra.mahler_center_fiber_join import (
    MahlerCenterFiberEdge,
)
from number_compiler.sequences.antihydra.mahler_joint_future import (
    MahlerJointFutureAction,
)
from number_compiler.sequences.antihydra.mahler_low_border_carry import (
    MahlerBorderCarryMap,
    MahlerLowBorderCarryCertificate,
    MahlerRadix4TwoTickCarry,
)
from number_compiler.sequences.antihydra.mahler_port_puncture import (
    MahlerCarryPortPuncture,
    MahlerCenterPortPuncture,
)

FULL = (1 << STATES) - 1
_MAHLER_CENTER_STATE_SPACE: BooleanStateSpace[int] = BooleanStateSpace(
    "antihydra.mahler-decimal-center", tuple(range(STATES))
)
MAX_CERTIFIED_TICKS = 32
MAX_POINTED_DIGITS = 256
_MAX_POINTED_SOURCE = 10**MAX_POINTED_DIGITS
_SOURCE_MATRIX_ISSUER = object()


def _word_bits(row: int) -> tuple[int, ...]:
    return tuple(i for i in range(STATES) if (row >> i) & 1)


@dataclass(frozen=True, slots=True, init=False)
class MahlerCenterBooleanMatrix:
    """100-state bitset relation; composition uses the Boolean semiring.

    Matrices constructed from supplied letters are conditional. Their powers
    are *only* powers of those hypothetical letters until a source owner
    authenticates each temporal inlet and width/recentering operation.
    """

    _relation: BooleanMatrix[int]

    def __init__(self, rows: tuple[int, ...]) -> None:
        object.__setattr__(
            self,
            "_relation",
            BooleanMatrix(_MAHLER_CENTER_STATE_SPACE, rows),
        )

    @classmethod
    def _from_relation(cls, relation: BooleanMatrix[int]) -> MahlerCenterBooleanMatrix:
        if (
            type(relation) is not BooleanMatrix
            or relation.state_space is not _MAHLER_CENTER_STATE_SPACE
        ):
            raise TypeError("Mahler matrix needs its decimal-center state space")
        result = object.__new__(cls)
        object.__setattr__(result, "_relation", relation)
        return result

    @property
    def rows(self) -> tuple[int, ...]:
        return self._relation.rows

    @property
    def state_space(self) -> BooleanStateSpace[int]:
        return self._relation.state_space

    @classmethod
    def identity(cls) -> MahlerCenterBooleanMatrix:
        return cls._from_relation(
            BooleanMatrix[int].identity(_MAHLER_CENTER_STATE_SPACE)
        )

    @classmethod
    def from_driver(
        cls, lower_carry: int, upper_parity: int
    ) -> MahlerCenterBooleanMatrix:
        """One of the six exact total 100x100 matrices (all 100 rows)."""
        return cls(
            tuple(1 << center_next(i, lower_carry, upper_parity) for i in range(STATES))
        )

    @classmethod
    def from_contexts(
        cls, letters: tuple[tuple[int, int], ...]
    ) -> MahlerCenterBooleanMatrix:
        """Union of admitted but as-yet-unresolved carry-inlet letters."""
        if type(letters) is not tuple or not letters:
            raise ValueError("a nonempty typed center driver alphabet is required")
        rows = [0] * STATES
        for letter in letters:
            if type(letter) is not tuple or len(letter) != 2:
                raise TypeError(
                    "center input letters must be typed (carry,parity) pairs"
                )
            carry, parity = letter
            # Let the single-letter validator authenticate all inputs.
            center_next(0, carry, parity)
            for state in range(STATES):
                rows[state] |= 1 << center_next(state, carry, parity)
        return cls(tuple(rows))

    @classmethod
    def from_exterior(
        cls, join: object, *, admitted_only: bool = True
    ) -> MahlerCenterBooleanMatrix:
        """Intersect a genuine complete exterior source fiber with the matrix."""
        from number_compiler.sequences.antihydra.mahler_center_exterior_join import (
            MahlerCenterExteriorEvidence,
        )

        if type(admitted_only) is not bool:
            raise TypeError("center candidate admission flag must be Boolean")
        evidence = MahlerCenterExteriorEvidence.from_join(join)
        join = evidence.join
        if join.center_places != 2:
            raise TypeError("100x100 matrix needs an issued two-digit exterior join")
        low_border = MahlerLowBorderCarryCertificate.from_verified_evidence(evidence)
        rows = [0] * STATES
        allowed = set(
            join.source_admitted_centers
            if admitted_only
            else (item.center for item in join.candidates)
        )
        upper_parity = (join.authenticated_source // 10 ** (join.center_start + 2)) & 1
        for item in join.candidates:
            if item.center not in allowed:
                continue
            port = MahlerCenterPortPuncture.from_verified_evidence(
                evidence, item.center
            )
            if port.lower_carry != low_border.actual_carry:
                raise ArithmeticError("punctured lower carry differs from matrix inlet")
            expected, outgoing, next_upper = low_border.upper_transfer(
                item.center,
                join.authenticated_source // 10 ** (join.center_start + 2),
            )
            if (
                outgoing != item.upper_tripling_carry_out
                or next_upper != port.next_source // 10 ** (join.center_start + 2)
                or expected != item.next_fixed_center
                or port.center_upper_carry != outgoing
                or port.upper_division_inlet != ((upper_parity + outgoing) & 1)
                or expected != port.fixed_next_center
            ):
                raise ArithmeticError(
                    "conditional 100-state Mahler action disagrees with source ports"
                )
            rows[item.center] = 1 << port.fixed_next_center
        if not ((rows[join.pointed_center] >> join.pointed_next_center) & 1):
            raise ArithmeticError(
                "center relation discarded authentic pointed transition"
            )
        return cls(tuple(rows))

    @property
    def nonempty_rows(self) -> int:
        return sum(bool(row) for row in self.rows)

    @property
    def edges(self) -> int:
        return sum(row.bit_count() for row in self.rows)

    def destinations(self, source: int) -> tuple[int, ...]:
        if type(source) is not int or not 0 <= source < STATES:
            raise ValueError("matrix input center must be in 0..99")
        return _word_bits(self.rows[source])

    def apply_set(self, sources: int) -> int:
        return self._relation.image(sources)

    def then(self, after: MahlerCenterBooleanMatrix) -> MahlerCenterBooleanMatrix:
        """Boolean relational composition; source authority does NOT transfer."""
        if type(after) is not MahlerCenterBooleanMatrix:
            raise TypeError("center matrix requires a matching 100-state action")
        return self._from_relation(self._relation.then(after._relation))

    def power(self, repetitions: int) -> MahlerCenterBooleanMatrix:
        """Binary square a *hypothetical* repeated input letter program."""
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("nonnegative integral center matrix power required")
        return self._from_relation(self._relation.power(repetitions))

    def compact_packet(self, *, include_rows: bool = False) -> dict[str, object]:
        if type(include_rows) is not bool:
            raise TypeError("sparse matrix row demand must be Boolean")
        result: dict[str, object] = {
            "state_count": STATES,
            "conditional_moore_band_classes": len(conditional_center_moore()),
            "semiring": "Boolean (OR,AND)",
            "nonempty_rows": self.nonempty_rows,
            "nonzero_entries": self.edges,
            "source_authority": "matrix-relation-only; temporal repeat not certified",
            "temporal_repeat_certified": False,
        }
        if include_rows:
            result["sparse_rows"] = tuple(
                (source, _word_bits(row)) for source, row in enumerate(self.rows) if row
            )
        return result


@dataclass(frozen=True, slots=True)
class MahlerCertifiedCenterDepthTransfer:
    """A finite multi-tick center relation with full-source witnesses."""

    matrix: MahlerCenterBooleanMatrix
    safety_matrix: MahlerCenterBooleanMatrix
    steps: int
    pointed_sources: tuple[int, ...]
    pointed_centers: tuple[int, ...]
    center_positions: tuple[int, ...]
    radix99: tuple[int, ...]
    radix198: tuple[int, ...]
    rejected_source_paths: int
    width_births: tuple[int, ...]
    conditional_composition: MahlerCenterBooleanMatrix
    initial_ledger: int | None
    low_border_carries: tuple[MahlerLowBorderCarryCertificate | None, ...]
    source_port_punctures: tuple[tuple[MahlerCenterPortPuncture, ...], ...]
    source_fiber_edges: tuple[MahlerCenterFiberEdge, ...]
    composition_joins: int = 0
    equal_span_joins: int = 0
    _issuer: object = field(default=None, init=False, repr=False, compare=False)
    _issuance_snapshot: tuple[int, tuple[object, ...]] | None = field(
        default=None, init=False, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        # A certificate's public fields are convenient to inspect, but a
        # caller-assembled record must not publish as source authority.
        if self._issuer is not _SOURCE_MATRIX_ISSUER:
            raise ValueError("Mahler center trace must come from a source issuer")

    @classmethod
    def _issue(
        cls,
        *,
        matrix: MahlerCenterBooleanMatrix,
        safety_matrix: MahlerCenterBooleanMatrix,
        steps: int,
        pointed_sources: tuple[int, ...],
        pointed_centers: tuple[int, ...],
        center_positions: tuple[int, ...],
        radix99: tuple[int, ...],
        radix198: tuple[int, ...],
        rejected_source_paths: int,
        width_births: tuple[int, ...],
        conditional_composition: MahlerCenterBooleanMatrix,
        initial_ledger: int | None,
        low_border_carries: tuple[MahlerLowBorderCarryCertificate | None, ...],
        source_port_punctures: tuple[tuple[MahlerCenterPortPuncture, ...], ...],
        source_fiber_edges: tuple[MahlerCenterFiberEdge, ...],
        composition_joins: int = 0,
        equal_span_joins: int = 0,
    ) -> MahlerCertifiedCenterDepthTransfer:
        """Seal a relation after its fields have been checked by an issuer."""
        from number_compiler.sequences.antihydra.mahler_center_fiber_join import (
            allocate_transfer_fields,
        )

        fields: dict[str, object] = {
            "matrix": matrix,
            "safety_matrix": safety_matrix,
            "steps": steps,
            "pointed_sources": pointed_sources,
            "pointed_centers": pointed_centers,
            "center_positions": center_positions,
            "radix99": radix99,
            "radix198": radix198,
            "rejected_source_paths": rejected_source_paths,
            "width_births": width_births,
            "conditional_composition": conditional_composition,
            "initial_ledger": initial_ledger,
            "low_border_carries": low_border_carries,
            "source_port_punctures": source_port_punctures,
            "source_fiber_edges": source_fiber_edges,
            "composition_joins": composition_joins,
            "equal_span_joins": equal_span_joins,
        }
        result = allocate_transfer_fields(cls, fields)
        object.__setattr__(result, "_issuer", _SOURCE_MATRIX_ISSUER)
        names = tuple(fields)
        snapshot = tuple(
            cls._snapshot_value(getattr(result, name), name) for name in names
        )
        object.__setattr__(result, "_issuance_snapshot", (id(result), snapshot))
        return result

    @staticmethod
    def _tag(value: object) -> tuple[type[object], object]:
        return type(value), value

    @classmethod
    def _snapshot_low_carry(cls, value: object) -> object:
        if type(value) is not MahlerLowBorderCarryCertificate:
            return type(value), id(value)
        action = value.carry_map
        action_snapshot: object = (type(action), id(action))
        if type(action) is MahlerBorderCarryMap:
            action_snapshot = (
                type(action),
                id(action),
                cls._tag(action.radix),
                cls._tag(action.multiplier),
                cls._tag(action.digits),
                cls._tag(action.responses),
                tuple(cls._tag(item) for item in action.responses)
                if type(action.responses) is tuple
                else None,
            )
        return (
            type(value),
            id(value),
            cls._tag(value.source),
            cls._tag(value.center_start),
            action_snapshot,
            cls._tag(value.actual_carry),
            cls._tag(value.motif_repetitions),
            cls._tag(value.compressed_motif_blocks),
        )

    @classmethod
    def _snapshot_seam(cls, value: object) -> object:
        if type(value) is not MahlerCarryPortPuncture:
            return type(value), id(value)
        responses = value.carry_responses
        return (
            type(value),
            id(value),
            cls._tag(value.start),
            cls._tag(value.width),
            cls._tag(value.kind),
            cls._tag(value.carry_in),
            cls._tag(value.carry_out),
            cls._tag(value.division_in),
            cls._tag(value.division_out),
            cls._tag(responses),
            tuple(cls._tag(item) for item in responses)
            if type(responses) is tuple
            else None,
        )

    @classmethod
    def _snapshot_port(cls, value: object) -> object:
        if type(value) is not MahlerCenterPortPuncture:
            return type(value), id(value)
        punctures = value.punctures
        puncture_snapshot = (
            tuple(cls._snapshot_seam(item) for item in punctures)
            if type(punctures) is tuple
            else (type(punctures), id(punctures))
        )
        return (
            type(value),
            id(value),
            cls._tag(value.source),
            cls._tag(value.center),
            cls._tag(value.fixed_next_center),
            cls._tag(value.next_source),
            cls._tag(value.lower_carry),
            cls._tag(value.center_upper_carry),
            cls._tag(value.upper_division_inlet),
            cls._tag(value.top_carry),
            puncture_snapshot,
        )

    @classmethod
    def _snapshot_value(cls, value: object, field_name: str = "") -> object:
        if field_name == "low_border_carries" and is_exact_object_tuple(value):
            return (
                "low-border-carry-tuple",
                tuple(
                    None if item is None else cls._snapshot_low_carry(item)
                    for item in value
                ),
            )
        if field_name == "source_port_punctures" and is_exact_object_tuple(value):
            frames = tuple(
                (
                    "puncture-frame",
                    tuple(cls._snapshot_port(item) for item in frame),
                )
                if is_exact_object_tuple(frame)
                else (type(frame), id(frame))
                for frame in value
            )
            return "source-port-punctures", frames
        if field_name == "source_fiber_edges" and is_exact_object_tuple(value):
            return (
                "source-fiber-edges",
                tuple(
                    (
                        type(edge),
                        id(edge),
                        cls._tag(edge.source),
                        cls._tag(edge.endpoint),
                        cls._tag(edge.future.semantic_id),
                        cls._tag(edge.ledger_delta),
                        cls._tag(edge.ledger_minimum),
                    )
                    if type(edge) is MahlerCenterFiberEdge
                    else (type(edge), id(edge))
                    for edge in value
                ),
            )
        if isinstance(value, MahlerCenterBooleanMatrix):
            return (
                "MahlerCenterBooleanMatrix",
                id(value),
                tuple((type(row), row) for row in value.rows),
            )
        if is_exact_object_tuple(value):
            return (
                "tuple",
                tuple((type(item), item) for item in value),
            )
        if value is None:
            return (None,)
        return (type(value), value)

    def require_issued(self) -> None:
        issuer = getattr(self, "_issuer", None)
        issuance_snapshot = getattr(self, "_issuance_snapshot", None)
        if issuer is not _SOURCE_MATRIX_ISSUER or issuance_snapshot != (
            id(self),
            (
                self._snapshot_value(self.matrix),
                self._snapshot_value(self.safety_matrix),
                self._snapshot_value(self.steps),
                self._snapshot_value(self.pointed_sources),
                self._snapshot_value(self.pointed_centers),
                self._snapshot_value(self.center_positions),
                self._snapshot_value(self.radix99),
                self._snapshot_value(self.radix198),
                self._snapshot_value(self.rejected_source_paths),
                self._snapshot_value(self.width_births),
                self._snapshot_value(self.conditional_composition),
                self._snapshot_value(self.initial_ledger),
                self._snapshot_value(self.low_border_carries, "low_border_carries"),
                self._snapshot_value(
                    self.source_port_punctures, "source_port_punctures"
                ),
                self._snapshot_value(self.source_fiber_edges, "source_fiber_edges"),
                self._snapshot_value(self.composition_joins),
                self._snapshot_value(self.equal_span_joins),
            ),
        ):
            raise ValueError("Mahler center trace is not source-issued")

    @classmethod
    def from_sources(
        cls,
        sources: tuple[int, ...],
        *,
        initial_ledger: int | None = None,
        pointed_futures: tuple[MahlerJointFutureAction, ...] | None = None,
    ) -> MahlerCertifiedCenterDepthTransfer:
        if (
            type(sources) is not tuple
            or not 2 <= len(sources) <= MAX_CERTIFIED_TICKS + 1
        ):
            raise BlockContextBudgetExceeded(
                "source-certified center matrix requires 1..32 pointed ticks"
            )
        if any(
            type(source) is not int or source < 1 or source >= _MAX_POINTED_SOURCE
            for source in sources
        ):
            raise BlockContextBudgetExceeded(
                "pointed source exceeds the 256-digit center matrix budget"
            )
        if initial_ledger is not None and type(initial_ledger) is not int:
            raise TypeError("ledger guard must be an exact integer or omitted")
        if pointed_futures is not None and (
            type(pointed_futures) is not tuple
            or len(pointed_futures) != len(sources) - 1
            or any(
                type(future) is not MahlerJointFutureAction
                for future in pointed_futures
            )
        ):
            raise ValueError("pointed source futures must cover each adjacent edge")
        if pointed_futures is not None:
            for future in pointed_futures:
                try:
                    future.__post_init__()
                except (AttributeError, TypeError, ValueError) as exc:
                    raise ValueError("pointed source future is malformed") from exc
        for index, (before, after) in enumerate(pairwise(sources)):
            if pointed_futures is None:
                admitted_endpoint = (3 * before + (before & 1)) // 2
            else:
                future = pointed_futures[index]
                if future.extent != 1 or not future.integer_admits(before):
                    raise ValueError(
                        "pointed future does not admit its exact source edge"
                    )
                admitted_endpoint = future.endpoint(before)
            if admitted_endpoint != after:
                raise ValueError("unverified center-matrix physical successor")

        from number_compiler.sequences.antihydra.mahler_center_exterior_join import (
            MahlerCenterExteriorEvidence,
        )

        # Use a fixed two-digit window beginning at the tens place for short
        # sources. The implied leading zeroes are exact decimal padding; they
        # do not create a source repeat or a guessed external carry.
        positions = tuple(max(1, (len(str(d)) - 2) // 2) for d in sources)
        # Keep the pointed exterior joins once: the lower carry and bilateral
        # seam records are shared by all center candidates at that source.
        candidate_sets_list: list[set[int]] = []
        pointed_centers_list: list[int] = []
        joins: list[MahlerCenterExteriorEvidence | None] = []
        for source, position in zip(sources, positions, strict=True):
            evidence: MahlerCenterExteriorEvidence | None
            if len(str(source)) >= 4:
                evidence = MahlerCenterExteriorEvidence.from_source(
                    source, center_places=2, center_start=position
                )
                join = evidence.join
                joins.append(evidence)
                candidate_sets_list.append(
                    {
                        source
                        + (candidate.center - join.pointed_center)
                        * 10**join.center_start
                        for candidate in join.candidates
                        if candidate.center in join.source_admitted_centers
                    }
                )
                pointed_centers_list.append(join.pointed_center)
            else:
                joins.append(None)
                # Zero padding makes this fixed two-digit window exact even
                # when the source has fewer than four decimal digits.
                candidate_sets_list.append({source})
                pointed_centers_list.append((source // 10**position) % 100)
        candidate_sets = tuple(candidate_sets_list)
        pointed_centers = tuple(pointed_centers_list)
        if not all(
            d in possible for d, possible in zip(sources, candidate_sets, strict=True)
        ):
            raise ArithmeticError(
                "pointed source excluded from a complete center fiber"
            )
        low_ports = tuple(
            None
            if evidence is None
            else MahlerLowBorderCarryCertificate.from_verified_evidence(evidence)
            for evidence in joins[:-1]
        )
        port_frames = tuple(
            ()
            if evidence is None
            else tuple(
                MahlerCenterPortPuncture.from_verified_evidence(
                    evidence, candidate.center
                )
                for candidate in evidence.join.candidates
                if candidate.center in evidence.join.source_admitted_centers
            )
            for evidence in joins[:-1]
        )
        port_tables = tuple(
            {port.source: port for port in frame} for frame in port_frames
        )
        for index, evidence in enumerate(joins[:-1]):
            if evidence is not None and sources[index] not in port_tables[index]:
                raise ArithmeticError(
                    "pointed center is missing its bilateral port witness"
                )
        # Each conditional step uses the 100x100 Mahler center transfer,
        # followed by a source-checked re-centering when the width changes.
        # Boolean composition is a *necessary* relation. It may contain
        # spliced aliases; full-source witnesses below remove those paths.
        conditional = MahlerCenterBooleanMatrix.identity()
        for index in range(len(sources) - 1):
            current_s = positions[index]
            next_s = positions[index + 1]
            step_rows = [0] * STATES
            for candidate in candidate_sets[index]:
                c = (candidate // 10**current_s) % 100
                low_base = 10**current_s
                upper = candidate // (100 * low_base)
                low_port = low_ports[index]
                if low_port is None:
                    lower = candidate % low_base
                    carry = (3 * lower + (candidate & 1)) // low_base
                    next_fixed = center_next(c, carry, upper & 1)
                    next_source = (3 * candidate + (candidate & 1)) // 2
                else:
                    if (candidate & 1) != (low_port.source & 1):
                        raise ArithmeticError(
                            "candidate changed its authenticated low inlet"
                        )
                    port = port_tables[index].get(candidate)
                    if port is None:
                        raise ArithmeticError("candidate has no bilateral port witness")
                    carry = low_port.actual_carry
                    next_fixed, outgoing, next_upper = low_port.upper_transfer(c, upper)
                    if (
                        port.lower_carry != carry
                        or port.center_upper_carry != outgoing
                        or port.upper_division_inlet != ((upper + outgoing) & 1)
                        or port.fixed_next_center != next_fixed
                        or port.next_source // (100 * low_base) != next_upper
                    ):
                        raise ArithmeticError(
                            "punctured ports disagree with matrix inputs"
                        )
                    next_source = port.next_source
                if next_fixed != (next_source // low_base) % 100:
                    raise ArithmeticError(
                        "100-state center transfer lost its exact carry"
                    )
                if MahlerCenterBooleanMatrix.from_driver(carry, upper & 1).destinations(
                    c
                ) != (next_fixed,):
                    raise ArithmeticError("center row ignored its certified low carry")
                if next_source in candidate_sets[index + 1]:
                    next_center = (next_source // 10**next_s) % 100
                    step_rows[c] |= 1 << next_center
            step_matrix = MahlerCenterBooleanMatrix(tuple(step_rows))
            conditional = conditional.then(step_matrix)
        arithmetic = [0] * STATES
        safety = [0] * STATES
        refused = 0
        exact_edges: list[MahlerCenterFiberEdge] = []
        for candidate in sorted(candidate_sets[0]):
            root_center = (candidate // 10 ** positions[0]) % 100
            at = candidate
            valid = True
            ledger_change = 0
            ledger_minimum = 0
            is_pointed_root = candidate == sources[0]
            pointed_future = MahlerJointFutureAction()
            for index in range(len(sources) - 1):
                if at not in candidate_sets[index]:
                    valid = False
                    break
                epsilon = at & 1
                port = port_tables[index].get(at)
                if low_ports[index] is not None and port is None:
                    valid = False
                    break
                if is_pointed_root and pointed_futures is not None:
                    edge_future = pointed_futures[index]
                    if not edge_future.integer_admits(at):
                        raise ArithmeticError(
                            "pointed source left its admitted successor fiber"
                        )
                    at_next = edge_future.endpoint(at)
                    pointed_future = pointed_future.then(edge_future)
                else:
                    at_next = (3 * at + epsilon) // 2
                if port is not None and at_next != port.next_source:
                    raise ArithmeticError(
                        "finite port witness changed a source successor"
                    )
                change = 3 * epsilon - 1
                ledger_change += change
                ledger_minimum = min(ledger_minimum, ledger_change)
                at = at_next
                if at not in candidate_sets[index + 1]:
                    valid = False
                    break
            if not valid:
                refused += 1
                continue
            target = (at // 10 ** positions[-1]) % 100
            arithmetic[root_center] |= 1 << target
            future = (
                pointed_future
                if is_pointed_root and pointed_futures is not None
                else MahlerJointFutureAction.from_source_prefix(
                    candidate, len(sources) - 1, max_steps=MAX_CERTIFIED_TICKS
                )
            )
            edge = MahlerCenterFiberEdge(
                candidate, at, future, ledger_change, ledger_minimum
            )
            exact_edges.append(edge)
            if not future.guard.empty and edge.ledger_safe(initial_ledger):
                safety[root_center] |= 1 << target
        for root_center, row in enumerate(arithmetic):
            if row & ~conditional.rows[root_center]:
                raise ArithmeticError(
                    "source-witnessed center path absent from Boolean matrix power"
                )
        actual_first = pointed_centers[0]
        actual_final = pointed_centers[-1]
        if not ((arithmetic[actual_first] >> actual_final) & 1):
            raise ArithmeticError("pointed full-source center path lost in transfer")
        births = tuple(
            i + 1
            for i in range(len(sources) - 1)
            if len(str(sources[i])) != len(str(sources[i + 1]))
        )
        # Issue only after deriving every public field from the validated
        # source path above. No private factory accepts arbitrary field values.
        return cls._issue(
            matrix=MahlerCenterBooleanMatrix(tuple(arithmetic)),
            safety_matrix=MahlerCenterBooleanMatrix(tuple(safety)),
            steps=len(sources) - 1,
            pointed_sources=sources,
            pointed_centers=pointed_centers,
            center_positions=positions,
            radix99=tuple(d % 99 for d in sources),
            radix198=tuple(d % 198 for d in sources),
            rejected_source_paths=refused,
            width_births=births,
            conditional_composition=conditional,
            initial_ledger=initial_ledger,
            low_border_carries=low_ports,
            source_port_punctures=port_frames,
            source_fiber_edges=tuple(exact_edges),
        )

    @classmethod
    def from_source(
        cls, source: int, steps: int, *, initial_ledger: int | None = None
    ) -> MahlerCertifiedCenterDepthTransfer:
        if type(steps) is not int or not 1 <= steps <= MAX_CERTIFIED_TICKS:
            raise ValueError("center transfer source demand needs 1..32 physical steps")
        if type(source) is not int or source <= 0:
            raise ValueError("positive pointed Mahler center source required")
        if source >= _MAX_POINTED_SOURCE:
            raise BlockContextBudgetExceeded(
                "pointed source exceeds the 256-digit center matrix budget"
            )
        sequence = [source]
        for _ in range(steps):
            next_source = (3 * sequence[-1] + (sequence[-1] & 1)) // 2
            sequence.append(next_source)
        return cls.from_sources(tuple(sequence), initial_ledger=initial_ledger)

    @classmethod
    def from_program(
        cls,
        program: object,
        tick: int,
        steps: int,
        *,
        initial_ledger: int | None = None,
    ) -> MahlerCertifiedCenterDepthTransfer:
        from number_compiler.sequences.antihydra.mahler_odd_program import (
            MahlerOddSourceProgram,
        )

        if type(program) is not MahlerOddSourceProgram:
            raise TypeError("center depth transfer needs a Mahler source-program view")
        if (
            type(tick) is not int
            or type(steps) is not int
            or steps < 1
            or steps > MAX_CERTIFIED_TICKS
            or tick < program.clock
            or tick + steps > program.ending_clock
        ):
            raise ValueError(
                "center depth matrix exceeds the certified program horizon"
            )
        return cls.from_sources(
            tuple(program.source_at_tick(tick + i) for i in range(steps + 1)),
            initial_ledger=initial_ledger,
        )

    def then(
        self, after: MahlerCertifiedCenterDepthTransfer
    ) -> MahlerCertifiedCenterDepthTransfer:
        """Join previously certified source fibers without reissuing cones."""
        from number_compiler.sequences.antihydra.mahler_center_fiber_join import (
            compose_transfers,
        )

        fields = compose_transfers(self, after)
        return type(self)._issue(
            matrix=fields.matrix,
            safety_matrix=fields.safety_matrix,
            steps=fields.steps,
            pointed_sources=fields.pointed_sources,
            pointed_centers=fields.pointed_centers,
            center_positions=fields.center_positions,
            radix99=fields.radix99,
            radix198=fields.radix198,
            rejected_source_paths=fields.rejected_source_paths,
            width_births=fields.width_births,
            conditional_composition=fields.conditional_composition,
            initial_ledger=fields.initial_ledger,
            low_border_carries=fields.low_border_carries,
            source_port_punctures=fields.source_port_punctures,
            source_fiber_edges=fields.source_fiber_edges,
            composition_joins=fields.composition_joins,
            equal_span_joins=fields.equal_span_joins,
        )

    def square_with(
        self, actual_next_half: MahlerCertifiedCenterDepthTransfer
    ) -> MahlerCertifiedCenterDepthTransfer:
        """Compose equal physical spans after checking the actual full-root seam."""
        if type(actual_next_half) is not MahlerCertifiedCenterDepthTransfer:
            raise TypeError("a source-certified second half is required")
        if self.steps != actual_next_half.steps:
            raise ValueError("square requires equal-length physical halves")
        return self.then(actual_next_half)

    @classmethod
    def powered_from_source(
        cls,
        source: int,
        physical_steps: int,
        *,
        initial_ledger: int | None = None,
        leaf_steps: int = 4,
    ) -> MahlerCertifiedCenterDepthTransfer:
        """Issue bounded leaves, then join true roots and their cached actions."""
        from number_compiler.sequences.antihydra.mahler_center_fiber_join import (
            powered_from_source,
        )

        return powered_from_source(
            cls,
            source,
            physical_steps,
            initial_ledger=initial_ledger,
            leaf_steps=leaf_steps,
        )

    @classmethod
    def power_of_two_from_source(
        cls,
        source: int,
        level: int,
        *,
        initial_ledger: int | None = None,
    ) -> MahlerCertifiedCenterDepthTransfer:
        """Certify 2**level real ticks, reissuing each later inlet at its root."""
        if type(level) is not int or not 0 <= level <= 5:
            raise ValueError("center-matrix square level must be in 0..5")
        physical_steps = 1 << level
        leaf_steps = 1 << max(0, min(level - 1, 2))
        return cls.powered_from_source(
            source,
            physical_steps,
            initial_ledger=initial_ledger,
            leaf_steps=leaf_steps,
        )

    @property
    def radix4_two_tick_ports(self) -> tuple[MahlerRadix4TwoTickCarry, ...]:
        """Build the separate G² spatial port lane only for an opted-in packet."""
        ports = tuple(
            MahlerRadix4TwoTickCarry.from_source(self.pointed_sources[index], digits=6)
            for index in range(0, self.steps - 1, 2)
        )
        for index, port in enumerate(ports):
            endpoint = self.pointed_sources[2 * index + 2]
            if port.high_after_two != endpoint // 4**port.low_digits:
                raise ArithmeticError("radix-4 two-step port lost its source endpoint")
        return ports

    def first_separating_port_punctures(
        self,
    ) -> tuple[tuple[dict[str, object], ...], ...]:
        frames: list[tuple[dict[str, object], ...]] = []
        for frame in self.source_port_punctures:
            separations: list[dict[str, object]] = []
            for index, left in enumerate(frame):
                for right in frame[index + 1 :]:
                    for left_seam, right_seam in zip(
                        left.punctures, right.punctures, strict=True
                    ):
                        left_signature = (
                            left_seam.carry_in,
                            left_seam.carry_out,
                            left_seam.division_in,
                            left_seam.division_out,
                            left_seam.carry_responses,
                        )
                        right_signature = (
                            right_seam.carry_in,
                            right_seam.carry_out,
                            right_seam.division_in,
                            right_seam.division_out,
                            right_seam.carry_responses,
                        )
                        if left_signature != right_signature:
                            separations.append(
                                {
                                    "centers": (left.center, right.center),
                                    "first_separating_digit": left_seam.start,
                                    "first_separating_span_width": left_seam.width,
                                    "left_port": left_signature,
                                    "right_port": right_signature,
                                }
                            )
                            break
            frames.append(tuple(separations))
        return tuple(frames)

    def packet(
        self, *, include_rows: bool = False, trace: bool = False
    ) -> dict[str, object]:
        from number_compiler.sequences.antihydra.mahler_center_packet import (
            center_transfer_packet,
        )

        return center_transfer_packet(self, include_rows=include_rows, trace=trace)


__all__ = [
    "STATES",
    "MahlerCenterBooleanMatrix",
    "MahlerCertifiedCenterDepthTransfer",
    "center_next",
    "conditional_center_moore",
]
