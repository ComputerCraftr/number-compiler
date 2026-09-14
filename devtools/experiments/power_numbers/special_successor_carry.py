"""Bounded audit of successor-quotient generators for Fermat/Mersenne.

The purpose of this probe is to identify *injectors* for the small binary-jump
machines, not to create another retained state.  It tests the same generator
families used elsewhere in the repository:

* successor-image set morphisms;
* quadratic field/Jacobi residue constraints;
* alternate-radix reinterpretation as a derived observer only;
* finite structured decision automata; and
* Boolean ANF complexity of image-membership predicates.

Nothing here promotes a prime-case identity through a composite candidate.  In
particular M11 is retained as the ring-safety counterexample.
"""

from __future__ import annotations

from functools import lru_cache, partial
from hashlib import sha256

from devtools.experiments.power_numbers.special_successor_models import (
    BoundaryConsumerQuotientAudit,
    CarryCyclotomicTransducerAudit,
    CarryHenselCyclotomicAudit,
    CarryPhaseRefinementAudit,
    CarryTemporalAutomatonAudit,
    CarryTransferAutomatonAudit,
)
from devtools.proofs.immutable_artifacts import REGISTRY, ArtifactKey
from devtools.proofs.oracles.special_binary_jump import (
    _fermat_carrier_proof,
    _mersenne_carrier_proof,
)
from devtools.proofs.quotient_synthesis import (
    ObserverFeature,
    synthesize_finite_quotient,
)
from number_compiler.arithmetic.carry.carry_normalization import (
    RadixCarryAction,
    RadixCarryBlock,
    normalization_carry_boundaries,
    normalize_cyclic_block,
    normalize_negacyclic_block,
)
from number_compiler.arithmetic.functions.finite_unary import (
    minimize_unary_moore,
    partition_equivalent,
    quotient_machine_from_moore,
    unary_image_filtration,
)
from number_compiler.arithmetic.polynomials.arithmetic_tile import (
    ArithmeticTile,
    ArithmeticTileSpec,
)
from number_compiler.arithmetic.polynomials.cyclotomic_carry import (
    CarryCyclotomicTransducer,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    cyclic_binary_square_add_projection,
    negacyclic_binary_square_projection,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock
from number_compiler.arithmetic.polynomials.two_primary_filtration import (
    pure_two_primary_image_filtration,
)


def _carry_artifact_key(kind: str, *recipe: object) -> ArtifactKey:
    encoded = repr(("special-carry-observation-v1", kind, *recipe)).encode("ascii")
    return ArtifactKey(kind, sha256(encoded).hexdigest())


@lru_cache(maxsize=4)
def _special_square_fields(family: str, parameter: int) -> tuple[tuple[int, ...], ...]:
    """Raw folded square fields for one bounded carrier, cached for research reuse."""
    family = str(family)
    parameter = int(parameter)
    proof = (
        _fermat_carrier_proof(parameter)
        if family == "fermat"
        else _mersenne_carrier_proof(parameter)
    )
    width = (1 << parameter) if family == "fermat" else parameter
    out: list[tuple[int, ...]] = []
    for value in proof.representatives:
        projection = (
            negacyclic_binary_square_projection(value, width)
            if family == "fermat"
            else cyclic_binary_square_add_projection(value, width, -2)
        )
        out.append(tuple(projection.field))
    return tuple(out)


def _special_width(family: str, parameter: int) -> int:
    return (1 << int(parameter)) if family == "fermat" else int(parameter)


def _coarse_carry_block_size(width: int) -> int:
    """Largest power-of-two block strictly below the spatial width."""
    width = int(width)
    if width <= 1:
        return 1
    return 1 << max(0, (width - 1).bit_length() - 1)


def _build_reachable_carry_interval(
    family: str, parameter: int, radix: int
) -> tuple[int, int, int]:
    """Reachable end-around carry interval for the bounded truth carrier.

    This is research instrumentation, not a production premise.  It gives the
    extensional carry-action/transducer exactly the carry domain that actually
    occurs on the complete bounded carrier under the selected radix
    reinterpretation.
    """
    family = str(family)
    parameter = int(parameter)
    radix = int(radix)
    values: set[int] = set()
    for field in _special_square_fields(family, parameter):
        block = RadixCarryBlock.from_coefficients(field, base=radix)
        normalization = (
            normalize_negacyclic_block(block)
            if family == "fermat"
            else normalize_cyclic_block(block)
        )
        values.update(normalization_carry_boundaries(field, normalization))
    if not values:
        raise AssertionError((family, parameter, radix))
    lo, hi = min(values), max(values)
    # The observed carry values are contiguous on every bounded special case;
    # require that rather than silently filling holes in the action domain.
    if values != set(range(lo, hi + 1)):
        raise AssertionError((family, parameter, radix, sorted(values)))
    return lo, hi, len(values)


def _reachable_carry_interval(
    family: str, parameter: int, radix: int
) -> tuple[int, int, int]:
    family, parameter, radix = str(family), int(parameter), int(radix)
    if family not in ("fermat", "mersenne") or parameter < 0 or radix < 2:
        raise ValueError((family, parameter, radix))
    row, _hit = REGISTRY.obtain(
        _carry_artifact_key("special-carry-interval", family, parameter, radix),
        partial(_build_reachable_carry_interval, family, parameter, radix),
    )
    return row


def _partition_successor_conflicts(
    keys: tuple[object, ...],
    transition: tuple[int, ...],
    outputs: tuple[object, ...],
) -> tuple[int, int]:
    classes: dict[object, int] = {}
    class_ids = tuple(classes.setdefault(key, len(classes)) for key in keys)
    signatures: dict[int, tuple[object, int]] = {}
    conflicts = 0
    for state, class_id in enumerate(class_ids):
        signature = (outputs[state], class_ids[transition[state]])
        previous = signatures.setdefault(class_id, signature)
        conflicts += int(previous != signature)
    return len(classes), conflicts


def _build_carry_action_word(
    family: str,
    parameter: int,
    radix: int,
    block_size: int,
) -> tuple[tuple[tuple[object, ...], ...], ...]:
    lo, hi, _count = _reachable_carry_interval(family, parameter, radix)
    width = _special_width(family, parameter)
    words: list[tuple[tuple[object, ...], ...]] = []
    for field in _special_square_fields(family, parameter):
        word: list[tuple[object, ...]] = []
        for start in range(0, width, int(block_size)):
            block = RadixCarryBlock.from_coefficients(
                field[start : start + int(block_size)],
                base=int(radix),
            )
            action = RadixCarryAction.from_block(
                block, incoming_min=lo, incoming_max=hi
            )
            word.append(action.canonical_key)
        words.append(tuple(word))
    return tuple(words)


def _carry_action_word(
    family: str,
    parameter: int,
    radix: int,
    block_size: int,
) -> tuple[tuple[tuple[object, ...], ...], ...]:
    family = str(family)
    parameter, radix, block_size = int(parameter), int(radix), int(block_size)
    if (
        family not in ("fermat", "mersenne")
        or parameter < 0
        or radix < 2
        or block_size < 1
    ):
        raise ValueError((family, parameter, radix, block_size))
    # Each action-word recipe is consumed once inside its isolated audit worker.
    # Publishing the potentially large M17 row in the process-wide artifact
    # registry would therefore pay a full immutability walk and retain the row
    # without serving a natural hit.  The small carry interval used while
    # constructing the word remains a shared immutable artifact because the
    # ordinary worker requests those recipes repeatedly.
    return _build_carry_action_word(family, parameter, radix, block_size)


@lru_cache(maxsize=1)
def carry_transfer_automaton_audits() -> tuple[CarryTransferAutomatonAudit, ...]:
    """Test true multi-valued carry-action words, including alternate radices."""
    rows: list[CarryTransferAutomatonAudit] = []
    for family, parameter in (
        ("fermat", 3),
        ("fermat", 4),
        ("mersenne", 7),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        proof = (
            _fermat_carrier_proof(parameter)
            if family == "fermat"
            else _mersenne_carrier_proof(parameter)
        )
        width = _special_width(family, parameter)
        block_size = _coarse_carry_block_size(width)
        for radix in (2, 3, 5, 7, 10):
            lo, hi, count = _reachable_carry_interval(family, parameter, radix)
            words = _carry_action_word(family, parameter, radix, block_size)
            classes, conflicts = _partition_successor_conflicts(
                words, proof.transition, proof.outputs
            )
            unique_actions: dict[tuple[object, ...], RadixCarryAction] = {}
            for field in _special_square_fields(family, parameter):
                for start in range(0, width, block_size):
                    block = RadixCarryBlock.from_coefficients(
                        field[start : start + block_size], base=radix
                    )
                    action = RadixCarryAction.from_block(
                        block, incoming_min=lo, incoming_max=hi
                    )
                    unique_actions.setdefault(action.canonical_key, action)
            average_bits = (
                sum(action.description_bits for action in unique_actions.values())
                / len(unique_actions)
                if unique_actions
                else 0.0
            )
            rows.append(
                CarryTransferAutomatonAudit(
                    family,
                    parameter,
                    radix,
                    block_size,
                    proof.classes,
                    count,
                    len(unique_actions),
                    classes,
                    conflicts,
                    conflicts == 0,
                    average_bits,
                )
            )
    return tuple(rows)


@lru_cache(maxsize=1)
def carry_cyclotomic_transducer_audits() -> tuple[CarryCyclotomicTransducerAudit, ...]:
    """Add the carry-polynomial emission to coarse radix carry actions."""
    rows: list[CarryCyclotomicTransducerAudit] = []
    for family, parameter in (("fermat", 4), ("mersenne", 11), ("mersenne", 13)):
        proof = (
            _fermat_carrier_proof(parameter)
            if family == "fermat"
            else _mersenne_carrier_proof(parameter)
        )
        width = _special_width(family, parameter)
        block_size = _coarse_carry_block_size(width)
        radix = 10
        lo, hi, count = _reachable_carry_interval(family, parameter, radix)
        for order in (2, 4, 8):
            words: list[tuple[tuple[object, ...], ...]] = []
            unique: dict[tuple[object, ...], CarryCyclotomicTransducer] = {}
            for field in _special_square_fields(family, parameter):
                word: list[tuple[object, ...]] = []
                for start in range(0, width, block_size):
                    transducer = CarryCyclotomicTransducer.from_coefficients(
                        field[start : start + block_size],
                        base=radix,
                        incoming_min=lo,
                        incoming_max=hi,
                        order=order,
                        modulus=2,
                    )
                    key = transducer.canonical_key
                    unique.setdefault(key, transducer)
                    word.append(key)
                words.append(tuple(word))
            classes, conflicts = _partition_successor_conflicts(
                tuple(words),
                proof.transition,
                proof.outputs,
            )
            average_bits = (
                sum(item.description_bits for item in unique.values()) / len(unique)
                if unique
                else 0.0
            )
            rows.append(
                CarryCyclotomicTransducerAudit(
                    family,
                    parameter,
                    radix,
                    block_size,
                    order,
                    2,
                    count,
                    len(unique),
                    classes,
                    conflicts,
                    conflicts == 0,
                    average_bits,
                )
            )
    return tuple(rows)


@lru_cache(maxsize=1)
def boundary_consumer_quotient_audits() -> tuple[BoundaryConsumerQuotientAudit, ...]:
    """Test the geometry-first consumer quotient without claiming closure.

    The exact ``(carry,payload)`` response is an explicit negative control: a
    response at any admitted port reconstructs the raw positional value.  The
    carry-only and carry-plus-harmonic rows then measure the two genuine
    extensional quotients already owned by production arithmetic.
    """
    rows: list[BoundaryConsumerQuotientAudit] = []
    for family, parameter in (
        ("fermat", 3),
        ("fermat", 4),
        ("mersenne", 7),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        proof = (
            _fermat_carrier_proof(parameter)
            if family == "fermat"
            else _mersenne_carrier_proof(parameter)
        )
        width = _special_width(family, parameter)
        spec = getattr(ArithmeticTileSpec, family)(width)
        source_intervals = tuple(
            ArithmeticTile.from_value(spec, value).step_with_carry_interval()[1]
            for value in proof.representatives
        )
        lo = min(interval[0] for interval in source_intervals)
        hi = max(interval[1] for interval in source_intervals)
        exact_by_raw: dict[int, tuple[tuple[int, int], ...]] = {}
        carry_keys: list[object] = []
        harmonic_keys: list[object] = []
        harmonic_order = 4
        for value in proof.representatives:
            step, transducer = ArithmeticTile.from_value(
                spec, value
            ).step_with_harmonic_consumer(
                incoming_min=lo,
                incoming_max=hi,
                order=harmonic_order,
                modulus=2,
            )
            block = step.normalization.block
            expected = (value * value + spec.addend) % spec.modulus
            if step.tile.residue != expected:
                raise AssertionError((family, parameter, value, step.tile.residue))
            response = tuple(
                (block.outgoing_carry(carry), block.normalized_payload(carry))
                for carry in range(lo, hi + 1)
            )
            previous = exact_by_raw.setdefault(block.raw_value, response)
            if previous != response:
                raise AssertionError("one raw product has inconsistent exact action")
            carry_keys.append(
                step.boundary_action(incoming_min=lo, incoming_max=hi).canonical_key
            )
            harmonic_keys.append(transducer.canonical_key)

        exact_actions = set(exact_by_raw.values())
        carry_classes, carry_conflicts = _partition_successor_conflicts(
            tuple(carry_keys), proof.transition, proof.outputs
        )
        harmonic_classes, harmonic_conflicts = _partition_successor_conflicts(
            tuple(harmonic_keys), proof.transition, proof.outputs
        )
        harmonic_noninjective = harmonic_classes < proof.classes
        rows.append(
            BoundaryConsumerQuotientAudit(
                family,
                parameter,
                proof.classes,
                len(exact_by_raw),
                len(exact_actions),
                len(exact_actions) == len(exact_by_raw),
                carry_classes,
                carry_conflicts,
                harmonic_order,
                harmonic_classes,
                harmonic_conflicts,
                harmonic_noninjective,
                # A bounded one-step congruence, if observed, is not a proof
                # of temporal composition or a scheduler family certificate.
                False,
            )
        )
    return tuple(rows)


def _carry_hensel_features(
    family: str,
    parameter: int,
) -> tuple[tuple[ObserverFeature, ...], tuple[ObserverFeature, ...]]:
    proof = (
        _fermat_carrier_proof(parameter)
        if family == "fermat"
        else _mersenne_carrier_proof(parameter)
    )
    width = _special_width(family, parameter)
    fields = _special_square_fields(family, parameter)
    carries: list[tuple[int, ...]] = []
    for field in fields:
        block = RadixCarryBlock.from_coefficients(field, base=2)
        normalization = (
            normalize_negacyclic_block(block)
            if family == "fermat"
            else normalize_cyclic_block(block)
        )
        carries.append(normalization_carry_boundaries(field, normalization)[1:])

    def features(
        prefix: str, rows: tuple[tuple[int, ...], ...]
    ) -> tuple[ObserverFeature, ...]:
        out: list[ObserverFeature] = []
        for bit in range(4):
            planes = tuple(
                tuple((int(value) >> bit) & 1 for value in row) for row in rows
            )
            for order in (2, 4, 8):
                values = tuple(
                    CyclotomicDigitBlock.from_coefficients(
                        plane,
                        order=order,
                        modulus=2,
                        length=width,
                    ).residue
                    for plane in planes
                )
                out.append(
                    ObserverFeature(
                        f"{prefix}.bit{bit}.cyclotomic{order}", values, order
                    )
                )
        for precision in (1, 2, 3, 4):
            modulus = 1 << precision
            for order in (2, 4, 8):
                values = tuple(
                    CyclotomicDigitBlock.from_coefficients(
                        tuple(int(value) % modulus for value in row),
                        order=order,
                        modulus=modulus,
                        length=width,
                    ).residue
                    for row in rows
                )
                out.append(
                    ObserverFeature(
                        f"{prefix}.2adic{precision}.cyclotomic{order}", values, order
                    )
                )
        return tuple(out)

    raw = features("raw-square", fields)
    carry = features("carry", tuple(carries))
    if len(raw) != len(carry) or len(raw) != 24 or len(proof.transition) != len(fields):
        raise AssertionError((family, parameter, len(raw), len(carry), len(fields)))
    return raw, carry


@lru_cache(maxsize=1)
def carry_hensel_cyclotomic_audits() -> tuple[CarryHenselCyclotomicAudit, ...]:
    rows: list[CarryHenselCyclotomicAudit] = []
    for family, parameter in (("fermat", 4), ("mersenne", 11), ("mersenne", 13)):
        proof = (
            _fermat_carrier_proof(parameter)
            if family == "fermat"
            else _mersenne_carrier_proof(parameter)
        )
        raw, carry = _carry_hensel_features(family, parameter)
        for name, features in (
            ("carry-only", carry),
            ("raw-square+carry", raw + carry),
        ):
            result = synthesize_finite_quotient(
                proof.transition, proof.outputs, features
            )
            rows.append(
                CarryHenselCyclotomicAudit(
                    family,
                    parameter,
                    name,
                    len(features),
                    result.selected_features,
                    result.classes,
                    result.closed,
                    result.noninjective,
                    result.unresolved_counterexamples,
                )
            )
    return tuple(rows)


def _partition_successor_conflicts_from_ids(
    class_ids: tuple[int, ...],
    transition: tuple[int, ...],
    outputs: tuple[object, ...],
) -> tuple[int, int]:
    signatures: dict[int, tuple[object, int]] = {}
    conflicts = 0
    for state, class_id in enumerate(class_ids):
        signature = (outputs[state], class_ids[transition[state]])
        previous = signatures.setdefault(class_id, signature)
        conflicts += int(previous != signature)
    return len(signatures), conflicts


def _temporal_marker_partition(
    marker: tuple[object, ...],
    transition: tuple[int, ...],
    outputs: tuple[object, ...],
    horizon: int,
) -> tuple[int, int]:
    class_ids = _temporal_marker_history_ids(marker, transition, horizon)
    return _partition_successor_conflicts_from_ids(class_ids, transition, outputs)


def _temporal_marker_closure(
    marker: tuple[object, ...],
    transition: tuple[int, ...],
    outputs: tuple[object, ...],
    max_horizon: int,
) -> tuple[int | None, int]:
    """Find the first successor-closed observer history incrementally.

    Recomputing ``H_h`` from scratch for every ``h`` is O(h^2 |S|) and leaves
    large temporary tuple churn on the M17 guard.  This routine extends the
    exact history partition one layer at a time, so the scan is O(h |S|) and
    retains only integer class ids.
    """
    max_horizon = int(max_horizon)
    if max_horizon < 1:
        raise ValueError(max_horizon)
    marker_ids = _partition_ids(marker)
    class_ids = marker_ids
    classes = len(set(class_ids))
    for horizon in range(1, max_horizon + 1):
        classes, conflicts = _partition_successor_conflicts_from_ids(
            class_ids,
            transition,
            outputs,
        )
        if conflicts == 0:
            return horizon, classes
        if horizon != max_horizon:
            keys = tuple(
                (marker_ids[state], class_ids[transition[state]])
                for state in range(len(transition))
            )
            class_ids = _partition_ids(keys)
    return None, classes


@lru_cache(maxsize=1)
def carry_temporal_automaton_audits() -> tuple[CarryTemporalAutomatonAudit, ...]:
    """Check whether coarse carry actions gain a *sub-depth* temporal memory."""
    rows: list[CarryTemporalAutomatonAudit] = []
    for family, parameter in (
        ("fermat", 3),
        ("fermat", 4),
        ("mersenne", 5),
        ("mersenne", 7),
        ("mersenne", 13),
        ("mersenne", 17),
    ):
        proof = (
            _fermat_carrier_proof(parameter)
            if family == "fermat"
            else _mersenne_carrier_proof(parameter)
        )
        width = _special_width(family, parameter)
        block_size = _coarse_carry_block_size(width)
        marker = _carry_action_word(family, parameter, 10, block_size)
        marker_classes = len(set(marker))
        theorem = pure_two_primary_image_filtration(family, parameter)
        target_depth = theorem.target_image_depth
        assert target_depth is not None
        closure_horizon, horizon_classes = _temporal_marker_closure(
            marker,
            proof.transition,
            proof.outputs,
            target_depth + 2,
        )
        moore = minimize_unary_moore(proof.transition, proof.outputs)
        rows.append(
            CarryTemporalAutomatonAudit(
                family,
                parameter,
                f"radix10-carry-action-B{block_size}",
                marker_classes,
                closure_horizon,
                horizon_classes,
                moore.classes,
                target_depth,
                closure_horizon is not None and closure_horizon < target_depth,
            )
        )
    # Composite adversary: a cheap boundary itinerary can close quickly on M11,
    # which is exactly why such closure must never be promoted to the prime theorem.
    family, parameter = "mersenne", 11
    proof = _mersenne_carrier_proof(parameter)
    boundary: list[int] = []
    for field in _special_square_fields(family, parameter):
        block = RadixCarryBlock.from_coefficients(field, base=10)
        boundary.append(normalize_cyclic_block(block).boundary_in)
    boundary_marker = tuple(boundary)
    closure_horizon, horizon_classes = _temporal_marker_closure(
        boundary_marker,
        proof.transition,
        proof.outputs,
        20,
    )
    rows.append(
        CarryTemporalAutomatonAudit(
            family,
            parameter,
            "radix10-boundary",
            len(set(marker)),
            closure_horizon,
            horizon_classes,
            minimize_unary_moore(proof.transition, proof.outputs).classes,
            None,
            False,
        )
    )
    return tuple(rows)


def _temporal_marker_histories(
    marker: tuple[object, ...],
    transition: tuple[int, ...],
    horizon: int,
) -> tuple[tuple[object, ...], ...]:
    """Materialize one bounded observer history for exact research proof."""
    out: list[tuple[object, ...]] = []
    for source in range(len(transition)):
        state = source
        history: list[object] = []
        for _ in range(int(horizon)):
            history.append(marker[state])
            state = transition[state]
        out.append(tuple(history))
    return tuple(out)


def _partition_ids(values: tuple[object, ...]) -> tuple[int, ...]:
    classes: dict[object, int] = {}
    return tuple(classes.setdefault(value, len(classes)) for value in values)


def _temporal_marker_history_ids(
    marker: tuple[object, ...],
    transition: tuple[int, ...],
    horizon: int,
) -> tuple[int, ...]:
    """Exact history partition without materializing history tuples.

    A length-``h`` observer history satisfies the recursion

        ``H_h(s) = (marker(s), H_(h-1)(T(s)))``.

    Canonicalizing that pair at each layer gives exactly the same equivalence
    relation as storing all ``h`` marker objects, but retains only one integer
    class id per source state.  This is important on M17, where the irrelevant
    carry phase has tens of thousands of history classes.
    """
    horizon = int(horizon)
    if horizon < 0:
        raise ValueError(horizon)
    if len(marker) != len(transition):
        raise ValueError((len(marker), len(transition)))
    if horizon == 0:
        return (0,) * len(transition)
    marker_ids = _partition_ids(marker)
    ids = marker_ids
    for _ in range(1, horizon):
        keys = tuple(
            (marker_ids[state], ids[transition[state]])
            for state in range(len(transition))
        )
        ids = _partition_ids(keys)
    return ids


@lru_cache(maxsize=1)
def carry_phase_refinement_audits() -> tuple[CarryPhaseRefinementAudit, ...]:
    """Test whether carry history is redundant phase over independent depth.

    Depth comes exclusively from ``unary_image_filtration`` and the horizon
    comes from the independent prime-domain group theorem.  No marker value is
    designated as a target event.  Thus this experiment can only show that
    carry/radix history refines and then minimizes back to already-proved depth;
    it cannot circularly define that depth.
    """
    rows: list[CarryPhaseRefinementAudit] = []
    for family, parameter in (
        ("fermat", 3),
        ("fermat", 4),
        ("mersenne", 5),
        ("mersenne", 7),
        ("mersenne", 13),
        ("mersenne", 17),
    ):
        proof = (
            _fermat_carrier_proof(parameter)
            if family == "fermat"
            else _mersenne_carrier_proof(parameter)
        )
        filtration = unary_image_filtration(proof.transition)
        depth_ids = filtration.depth_ids
        theorem = pure_two_primary_image_filtration(family, parameter)
        target_depth = theorem.target_image_depth
        assert target_depth is not None
        history_horizon = target_depth + 1
        # M17 is the large-case scalability guard.  Canonical radix 2 checks
        # the canonical normalization shadow and radix 10 checks the strongest
        # compressed reinterpretation without multiplying the bounded proof cost
        # by five.  Smaller fixtures retain the full radix family.
        radices = (
            (2, 10) if family == "mersenne" and parameter == 17 else (2, 3, 5, 7, 10)
        )
        for radix in radices:
            marker = _carry_action_word(
                family,
                parameter,
                radix,
                _coarse_carry_block_size(_special_width(family, parameter)),
            )
            history_ids = _temporal_marker_history_ids(
                marker,
                proof.transition,
                history_horizon,
            )
            history_machine = quotient_machine_from_moore(
                proof.transition,
                proof.outputs,
                history_ids,
            )
            history_min = minimize_unary_moore(
                history_machine.transition,
                history_machine.outputs,
            )
            minimized_state_ids = tuple(
                history_min.class_ids[history_ids[state]]
                for state in range(proof.classes)
            )
            history_refines_depth = True
            seen_depth: dict[int, int] = {}
            phase_fibers: dict[int, set[int]] = {}
            for history_class, depth in zip(history_ids, depth_ids, strict=True):
                old = seen_depth.setdefault(history_class, depth)
                if old != depth:
                    history_refines_depth = False
                    break
                phase_fibers.setdefault(depth, set()).add(history_class)
            max_finite_phase_fiber = max(
                (len(classes) for depth, classes in phase_fibers.items() if depth >= 0),
                default=0,
            )
            stable_phase_classes = len(phase_fibers.get(-1, set()))

            rows.append(
                CarryPhaseRefinementAudit(
                    family,
                    parameter,
                    radix,
                    len(set(marker)),
                    history_horizon,
                    len(set(history_ids)),
                    len(set(depth_ids)),
                    history_refines_depth,
                    history_min.classes,
                    partition_equivalent(minimized_state_ids, depth_ids),
                    len(set(history_ids)) - len(set(depth_ids)),
                    max_finite_phase_fiber,
                    stable_phase_classes,
                    target_depth,
                )
            )
    return tuple(rows)
