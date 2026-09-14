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

from collections import deque
from math import prod
from typing import cast

from devtools.experiments.power_numbers.special_successor_models import (
    BooleanSetAudit,
    CRTPurityAudit,
    ImageFiltrationAudit,
    LocalTwoPrimaryComponent,
    PrimeGroupDepthAudit,
    ResidueConstraintAudit,
    StaticInjectionAudit,
    StructuredAutomatonAudit,
)
from devtools.proofs.oracles.special_binary_jump import (
    _fermat_carrier_proof,
    _mersenne_carrier_proof,
    fermat_radix_orbit_representative,
    mersenne_sign_representative,
)
from devtools.proofs.quotient_synthesis import (
    ObserverFeature,
    synthesize_finite_target_observer,
)
from number_compiler.arithmetic.fields.congruence_automaton import (
    reinterpret_binary_digits,
)
from number_compiler.arithmetic.functions.finite_unary import (
    minimize_unary_moore,
    partition_equivalent,
    quotient_machine_from_moore,
    unary_image_filtration,
)
from number_compiler.arithmetic.polynomials.two_primary_filtration import (
    pure_two_primary_image_filtration,
)
from number_compiler.sequences.prime.automaton import boolean_anf_metrics
from number_compiler.sequences.prime.set import jacobi_symbol, smallest_factor


def _target_conflicts(values: tuple[object, ...], labels: tuple[bool, ...]) -> int:
    seen: dict[object, bool] = {}
    conflicts = 0
    for key, label in zip(values, labels, strict=True):
        if key in seen:
            conflicts += int(seen[key] != label)
        else:
            seen[key] = label
    return conflicts


def _image_audit(family: str, parameter: int, prime_case: bool) -> ImageFiltrationAudit:
    proof = (
        _mersenne_carrier_proof(parameter, max_exponent=max(19, parameter))
        if family == "mersenne"
        else _fermat_carrier_proof(parameter, max_width=max(16, 1 << parameter))
    )
    moore = minimize_unary_moore(proof.transition, proof.outputs)
    filtration = unary_image_filtration(proof.transition)
    source_depth = filtration.depth_ids[proof.source_carrier]
    target_depths = tuple(
        sorted(
            {
                filtration.depth_ids[index]
                for index, output in enumerate(proof.outputs)
                if output
            }
        )
    )
    return ImageFiltrationAudit(
        family,
        parameter,
        proof.classes,
        moore.classes,
        filtration.ranks,
        filtration.stable_states,
        filtration.finite_depths,
        partition_equivalent(moore.class_ids, filtration.depth_ids),
        source_depth,
        target_depths,
        bool(prime_case),
    )


def image_filtration_audits() -> tuple[ImageFiltrationAudit, ...]:
    return (
        _image_audit("fermat", 3, True),
        _image_audit("fermat", 4, True),
        _image_audit("mersenne", 7, True),
        _image_audit("mersenne", 11, False),
        _image_audit("mersenne", 13, True),
        _image_audit("mersenne", 17, True),
    )


def _mersenne_jacobi_pair(exponent: int) -> tuple[tuple[int, int], ...]:
    p = int(exponent)
    modulus = (1 << p) - 1
    return tuple(
        cast(
            tuple[int, int],
            tuple(
                sorted((jacobi_symbol(x + 2, modulus), jacobi_symbol(2 - x, modulus)))
            ),
        )
        for x in range((modulus + 1) // 2)
    )


def residue_constraint_audits() -> tuple[ResidueConstraintAudit, ...]:
    rows: list[ResidueConstraintAudit] = []
    # Mersenne: the sign-invariant pair of square-existence characters for
    # y^2 = 2 +/- x is exact over prime fields for both the first image and the
    # split/nonsplit stable-core boundary.  M11 demonstrates why +1 cannot be
    # promoted through a composite ring.
    for p, prime_case in ((7, True), (11, False), (13, True), (17, True)):
        proof = _mersenne_carrier_proof(p, max_exponent=max(19, p))
        filt = unary_image_filtration(proof.transition)
        first_image = {proof.transition[state] for state in range(proof.classes)}
        stable = {state for state, depth in enumerate(filt.depth_ids) if depth < 0}
        values = _mersenne_jacobi_pair(p)
        for name, target in (("first_image", first_image), ("stable_core", stable)):
            labels = tuple(state in target for state in range(proof.classes))
            conflicts = _target_conflicts(values, labels)
            rows.append(
                ResidueConstraintAudit(
                    "mersenne",
                    p,
                    "unordered Jacobi(2+x),Jacobi(2-x)",
                    name,
                    len(target),
                    len(set(values)),
                    conflicts,
                    conflicts == 0,
                    # (-1,-1) is a sound no-predecessor certificate for every odd ring.
                    name == "first_image",
                )
            )
    # Fermat: radix phases have Jacobi(2/F_n)=+1 for n>=2, so Jacobi(x/F_n)=-1
    # is a sound no-square/no-first-image certificate even for composite F_n.
    for n in (3, 4):
        proof = _fermat_carrier_proof(n)
        modulus = (1 << (1 << n)) + 1
        first_image = {proof.transition[state] for state in range(proof.classes)}
        fermat_values = tuple(
            jacobi_symbol(rep, modulus) for rep in proof.representatives
        )
        labels = tuple(state in first_image for state in range(proof.classes))
        conflicts = _target_conflicts(fermat_values, labels)
        rows.append(
            ResidueConstraintAudit(
                "fermat",
                n,
                "Jacobi(binary-value,F_n)",
                "first_image",
                len(first_image),
                len(set(fermat_values)),
                conflicts,
                conflicts == 0,
                True,
            )
        )

        # Cross-base string reinterpretation is observer-only.  The deepest
        # bounded image can be separated cheaply, but this is not an arithmetic
        # homomorphism and is therefore retained only as a search constraint.
        stable = {
            state
            for state, depth in enumerate(
                unary_image_filtration(proof.transition).depth_ids
            )
            if depth < 0
        }
        encoded = tuple(
            reinterpret_binary_digits(rep, 7) for rep in proof.representatives
        )
        cross = tuple(
            (jacobi_symbol(v, modulus), jacobi_symbol(v - 1, modulus)) for v in encoded
        )
        stable_labels = tuple(state in stable for state in range(proof.classes))
        cconf = _target_conflicts(cross, stable_labels)
        rows.append(
            ResidueConstraintAudit(
                "fermat",
                n,
                "base7-string Jacobi(v),Jacobi(v-1)",
                "stable_core",
                len(stable),
                len(set(cross)),
                cconf,
                cconf == 0,
                False,
            )
        )
    return tuple(rows)


def _fermat_static_features(index: int) -> tuple[ObserverFeature, ...]:
    proof = _fermat_carrier_proof(index)
    modulus = (1 << (1 << index)) + 1
    reps = proof.representatives
    features: list[ObserverFeature] = []
    for base in (2, 3, 5, 7, 10):
        encoded = tuple(
            rep if base == 2 else reinterpret_binary_digits(rep, base) for rep in reps
        )
        trip = tuple(
            (
                jacobi_symbol(v - 1, modulus),
                jacobi_symbol(v, modulus),
                jacobi_symbol(v + 1, modulus),
            )
            for v in encoded
        )
        features.append(ObserverFeature(f"base{base}.jacobi_triplet", trip, 6))
    encoded7 = tuple(reinterpret_binary_digits(rep, 7) for rep in reps)
    for shift in (-8, 3, 7):
        features.append(
            ObserverFeature(
                f"base7.jacobi_shift_{shift}",
                tuple(jacobi_symbol(value + shift, modulus) for value in encoded7),
                2,
            )
        )
    return tuple(features)


def _mersenne_static_features(exponent: int) -> tuple[ObserverFeature, ...]:
    p = int(exponent)
    modulus = (1 << p) - 1
    reps = tuple(range((modulus + 1) // 2))
    features: list[ObserverFeature] = []
    for shift in range(-12, 13):
        features.append(
            ObserverFeature(
                f"sign_jacobi_shift_{shift}",
                tuple(
                    tuple(
                        sorted(
                            (
                                jacobi_symbol(x + shift, modulus),
                                jacobi_symbol((-x) % modulus + shift, modulus),
                            )
                        )
                    )
                    for x in reps
                ),
                2,
            )
        )
    for a, c in ((-2, 2), (1, -1), (1, 1), (0, 2), (0, -2)):
        values = []
        for x in reps:
            pair = []
            for y in (x, (-x) % modulus):
                pair.append(jacobi_symbol(y * y + a * y + c, modulus))
            values.append(tuple(sorted(pair)))
        features.append(ObserverFeature(f"sign_jacobi_quad_{a}_{c}", tuple(values), 2))
    return tuple(features)


def static_injection_audits() -> tuple[StaticInjectionAudit, ...]:
    rows = []
    for family, parameter in (
        ("fermat", 3),
        ("fermat", 4),
        ("mersenne", 7),
        ("mersenne", 13),
    ):
        proof = (
            _fermat_carrier_proof(parameter)
            if family == "fermat"
            else _mersenne_carrier_proof(parameter)
        )
        moore = minimize_unary_moore(proof.transition, proof.outputs)
        features = (
            _fermat_static_features(parameter)
            if family == "fermat"
            else _mersenne_static_features(parameter)
        )
        result = synthesize_finite_target_observer(moore.class_ids, features)
        rows.append(
            StaticInjectionAudit(
                family,
                parameter,
                "cross-base/Jacobi derived observers",
                proof.classes,
                moore.classes,
                result.selected_features,
                result.classes,
                result.target_separating,
                result.noninjective,
            )
        )
    return tuple(rows)


def _raw_class_labels(family: str, parameter: int) -> tuple[tuple[int, ...], int]:
    if family == "mersenne":
        p = int(parameter)
        modulus = (1 << p) - 1
        proof = _mersenne_carrier_proof(p)
        moore = minimize_unary_moore(proof.transition, proof.outputs)
        labels = tuple(
            moore.class_ids[mersenne_sign_representative(value, p)]
            for value in range(modulus)
        )
        return labels, moore.classes
    n = int(parameter)
    width = 1 << n
    modulus = (1 << width) + 1
    proof = _fermat_carrier_proof(n)
    moore = minimize_unary_moore(proof.transition, proof.outputs)
    _by_rep = {rep: index for index, rep in enumerate(proof.representatives)}
    raw_labels = [0] * modulus
    for carrier, rep in enumerate(proof.representatives):
        current = rep
        while True:
            raw_labels[current] = moore.class_ids[carrier]
            current = (2 * current) % modulus
            if current == rep:
                break
    return tuple(raw_labels), moore.classes


def _base_digits_domain(length: int, base: int) -> tuple[int, ...]:
    out = []
    domain = 1
    while domain < length:
        out.append(int(base))
        domain *= int(base)
    return tuple(out)


def _decision_dag_metrics(
    labels: tuple[int, ...], bases: tuple[int, ...], *, lsf: bool
) -> tuple[int, int]:
    domain = prod(bases)
    padded = labels + (-1,) * (domain - len(labels))
    strides = []
    stride = 1
    for base in bases:
        strides.append(stride)
        stride *= base
    order = tuple(range(len(bases))) if lsf else tuple(reversed(range(len(bases))))
    tables: list[dict[tuple[object, ...], int]] = [{} for _ in order]
    terminals: dict[int, int] = {}

    _root = (0, 0)
    memo: dict[tuple[int, int], tuple[str, int] | tuple[str, int, int]] = {}
    stack: list[tuple[int, int, bool]] = [(0, 0, False)]
    while stack:
        level, index, expanded = stack.pop()
        state = (level, index)
        if state in memo:
            continue
        if level == len(order):
            label = padded[index]
            memo[state] = ("t", terminals.setdefault(label, len(terminals)))
            continue
        pos = order[level]
        step = strides[pos]
        base = bases[pos]
        child_states = tuple((level + 1, index + digit * step) for digit in range(base))
        if not expanded:
            stack.append((level, index, True))
            for child in reversed(child_states):
                stack.append((child[0], child[1], False))
            continue
        children = tuple(memo[child] for child in child_states)
        table = tables[level]
        memo[state] = ("n", level, table.setdefault(children, len(table)))
    counts = tuple(len(table) for table in tables)
    return sum(counts) + len(terminals), max(counts, default=0)


def structured_automaton_audits() -> tuple[StructuredAutomatonAudit, ...]:
    rows = []
    for family, parameter in (
        ("fermat", 3),
        ("fermat", 4),
        ("mersenne", 7),
        ("mersenne", 13),
    ):
        labels, classes = _raw_class_labels(family, parameter)
        best: tuple[int, int, int, str] | None = None
        for base in (2, 3, 5, 7, 10):
            bases = _base_digits_domain(len(labels), base)
            for direction, lsf in (("lsf", True), ("msf", False)):
                nodes, max_level = _decision_dag_metrics(labels, bases, lsf=lsf)
                row = (nodes, max_level, base, direction)
                if best is None or row < best:
                    best = row
        assert best is not None
        nodes, max_level, base, direction = best
        rows.append(
            StructuredAutomatonAudit(
                family,
                parameter,
                len(labels),
                classes,
                base,
                direction,
                nodes,
                max_level,
                nodes / len(labels),
            )
        )
    return tuple(rows)


def boolean_set_audits() -> tuple[BooleanSetAudit, ...]:
    rows = []
    # Choose a middle layer where a low-degree Boolean-vector morphism would be
    # most valuable.  Use power-of-two domains only: M13 sign carrier and the
    # ordinary 16-bit slice of F4 (the exceptional -1 residue is excluded).
    p = 13
    proof = _mersenne_carrier_proof(p)
    filt = unary_image_filtration(proof.transition)
    level = 6
    target = {
        state
        for state, depth in enumerate(filt.depth_ids)
        if depth < 0 or depth >= level
    }
    mask = sum(1 << state for state in target)
    anf = boolean_anf_metrics(mask, p - 1)
    rows.append(
        BooleanSetAudit("mersenne", p, level, p - 1, len(target), anf.degree, anf.terms)
    )

    n = 4
    width = 1 << n
    proof = _fermat_carrier_proof(n)
    filt = unary_image_filtration(proof.transition)
    level = 6
    target_carriers = {
        state
        for state, depth in enumerate(filt.depth_ids)
        if depth < 0 or depth >= level
    }
    by_rep = {rep: state for state, rep in enumerate(proof.representatives)}
    mask = 0
    count = 0
    for value in range(1 << width):
        rep = fermat_radix_orbit_representative(value, n)
        if by_rep[rep] in target_carriers:
            mask |= 1 << value
            count += 1
    anf = boolean_anf_metrics(mask, width)
    rows.append(
        BooleanSetAudit("fermat", n, level, width, count, anf.degree, anf.terms)
    )
    return tuple(rows)


def _exact_target_hitting_times(
    transition: tuple[int, ...],
    outputs: tuple[bool, ...],
) -> tuple[int | None, ...]:
    """Return exact first target-hitting times in O(|S|) by reverse BFS.

    This semantic helper depends only on the unary transition and output
    predicate.  It deliberately does not inspect carry markers, image-depth
    labels, factorization, or any prime-domain theorem.
    """
    n = len(transition)
    if len(outputs) != n or any(not 0 <= nxt < n for nxt in transition):
        raise ValueError((n, len(outputs)))
    reverse: list[list[int]] = [[] for _ in range(n)]
    for state, nxt in enumerate(transition):
        reverse[nxt].append(state)
    distance: list[int | None] = [None] * n
    queue: deque[int] = deque()
    for state, output in enumerate(outputs):
        if output:
            distance[state] = 0
            queue.append(state)
    while queue:
        state = queue.popleft()
        current = distance[state]
        if current is None:
            raise AssertionError(state)
        for predecessor in reverse[state]:
            if distance[predecessor] is None:
                distance[predecessor] = current + 1
                queue.append(predecessor)
    return tuple(distance)


def prime_group_depth_audits() -> tuple[PrimeGroupDepthAudit, ...]:
    """Verify the prime-domain group theorem against complete bounded machines.

    The theorem itself is algebraic and contains the closed image-rank and
    depth-to-target-distance formulas.  The bounded machines are used only as
    differential proof fixtures; carry observers and carry-event timestamps do
    not participate in either side of the comparison.
    """
    rows: list[PrimeGroupDepthAudit] = []
    for family, parameter in (
        ("fermat", 2),
        ("fermat", 3),
        ("fermat", 4),
        ("mersenne", 5),
        ("mersenne", 7),
        ("mersenne", 13),
        ("mersenne", 17),
    ):
        theorem = pure_two_primary_image_filtration(family, parameter)
        proof = (
            _fermat_carrier_proof(parameter)
            if family == "fermat"
            else _mersenne_carrier_proof(parameter, max_exponent=max(19, parameter))
        )
        moore = minimize_unary_moore(proof.transition, proof.outputs)
        bounded_machine = quotient_machine_from_moore(
            proof.transition, proof.outputs, moore.class_ids
        )
        bounded_source = moore.class_ids[proof.source_carrier]
        filtration = unary_image_filtration(proof.transition)
        hitting_times = _exact_target_hitting_times(proof.transition, proof.outputs)
        target_depths = {
            filtration.depth_ids[index]
            for index, output in enumerate(proof.outputs)
            if output
        }
        if len(target_depths) != 1:
            raise AssertionError((family, parameter, target_depths))
        bounded_target_depth = next(iter(target_depths))
        predicted_ranks = theorem.image_ranks_through_stability()
        rank_formula_exact = predicted_ranks == filtration.ranks
        moore_equals_depth = partition_equivalent(moore.class_ids, filtration.depth_ids)
        target_distance_exact = all(
            hitting_times[state] == theorem.target_distance_from_depth(depth)
            for state, depth in enumerate(filtration.depth_ids)
        )

        mapping: dict[int, int] = {}
        reverse: dict[int, int] = {}
        assert theorem.machine is not None
        assert theorem.source_class is not None
        assert theorem.target_image_depth is not None
        theorem_state = theorem.source_class
        bounded_state = bounded_source
        consistent = True
        # One step beyond the target reaches the never class, so classes+1 is
        # sufficient to cover the entire chain and check absorbing behavior.
        for _ in range(theorem.machine.classes + 1):
            old_b = mapping.setdefault(theorem_state, bounded_state)
            old_t = reverse.setdefault(bounded_state, theorem_state)
            if old_b != bounded_state or old_t != theorem_state:
                consistent = False
                break
            if bool(theorem.machine.output(theorem_state)) != bool(
                bounded_machine.output(bounded_state)
            ):
                consistent = False
                break
            theorem_state = theorem.machine.transition[theorem_state]
            bounded_state = bounded_machine.transition[bounded_state]
        covers = len(mapping) == theorem.machine.classes == bounded_machine.classes
        rows.append(
            PrimeGroupDepthAudit(
                family,
                parameter,
                theorem.active_two_group_exponent,
                theorem.stable_image_states,
                theorem.quotient_classes,
                moore.classes,
                theorem.target_image_depth,
                bounded_target_depth,
                predicted_ranks,
                filtration.ranks,
                rank_formula_exact,
                moore_equals_depth,
                target_distance_exact,
                covers,
                consistent and covers,
                proof.classes,
            )
        )
    return tuple(rows)


def _v2_odd(value: int) -> tuple[int, int]:
    value = int(value)
    if value <= 0:
        raise ValueError(value)
    exponent = 0
    while not (value & 1):
        value >>= 1
        exponent += 1
    return exponent, value


def _factorization(value: int) -> tuple[tuple[int, int], ...]:
    """Complete bounded factorization for research truth labels only."""
    remaining = int(value)
    if remaining < 2:
        return ()
    out: list[tuple[int, int]] = []
    while remaining > 1:
        factor = smallest_factor(remaining)
        prime = remaining if factor is None else factor
        multiplicity = 0
        while remaining % prime == 0:
            remaining //= prime
            multiplicity += 1
        out.append((prime, multiplicity))
    return tuple(out)


def _prime_divisors(value: int) -> tuple[int, ...]:
    return tuple(prime for prime, _multiplicity in _factorization(value))


def _fermat_source_quotient_order(
    prime: int, parameter: int, quotient_order: int
) -> int:
    radix_order = 1 << (parameter + 1)
    radix_subgroup = {pow(2, exponent, prime) for exponent in range(radix_order)}
    order = int(quotient_order)
    for divisor in _prime_divisors(order):
        while (
            order % divisor == 0 and pow(3, order // divisor, prime) in radix_subgroup
        ):
            order //= divisor
    return order


def _quadratic_mul(
    first: tuple[int, int],
    second: tuple[int, int],
    delta: int,
    modulus: int,
) -> tuple[int, int]:
    a, b = first
    c, d = second
    return ((a * c + b * d * delta) % modulus, (a * d + b * c) % modulus)


def _quadratic_pow(
    value: tuple[int, int],
    exponent: int,
    delta: int,
    modulus: int,
) -> tuple[int, int]:
    result = (1, 0)
    base = value
    n = int(exponent)
    while n:
        if n & 1:
            result = _quadratic_mul(result, base, delta, modulus)
        n >>= 1
        if n:
            base = _quadratic_mul(base, base, delta, modulus)
    return result


def _mersenne_source_unit_order(prime: int, character: int, ambient_order: int) -> int:
    inv2 = pow(2, -1, prime)
    if character == 1:
        root = next(
            value for value in range(prime) if value * value % prime == 12 % prime
        )
        unit: int | tuple[int, int] = (4 + root) * inv2 % prime

        def power(exponent: int) -> object:
            assert isinstance(unit, int)
            return pow(unit, exponent, prime)

        one: object = 1
    elif character == -1:
        unit = (2 % prime, inv2)

        def power(exponent: int) -> object:
            return _quadratic_pow(unit, exponent, 12, prime)

        one = (1, 0)
    else:
        return 1
    order = int(ambient_order)
    for divisor in _prime_divisors(order):
        while order % divisor == 0 and power(order // divisor) == one:
            order //= divisor
    return order


def _crt_purity_audit(family: str, parameter: int) -> CRTPurityAudit:
    family = str(family)
    parameter = int(parameter)
    if family == "fermat":
        width = 1 << parameter
        modulus = (1 << width) + 1
    elif family == "mersenne":
        modulus = (1 << parameter) - 1
    else:
        raise ValueError(family)
    factors = _factorization(modulus)
    components: list[LocalTwoPrimaryComponent] = []
    obstructions: list[str] = []
    if len(factors) != 1 or factors[0][1] != 1:
        obstructions.append("multiple-or-repeated-crt-components")
    if family == "fermat":
        radix_order = 1 << (parameter + 1)
        expected_quotient = 1 << ((1 << parameter) - parameter - 1)
        for prime, multiplicity in factors:
            ambient = prime - 1
            av2, aodd = _v2_odd(ambient)
            if ambient % radix_order:
                raise AssertionError((family, parameter, prime, ambient, radix_order))
            quotient = ambient // radix_order
            qv2, qodd = _v2_odd(quotient)
            if qodd != 1:
                obstructions.append(f"odd-local-quotient:{prime}:{qodd}")
            source_order = _fermat_source_quotient_order(prime, parameter, quotient)
            sv2, sodd = _v2_odd(source_order)
            if sodd != 1:
                obstructions.append(f"odd-source-quotient-order:{prime}:{sodd}")
            components.append(
                LocalTwoPrimaryComponent(
                    prime,
                    multiplicity,
                    "multiplicative-field/radix-quotient",
                    None,
                    ambient,
                    av2,
                    aodd,
                    quotient,
                    qv2,
                    qodd,
                    source_order,
                    sv2,
                    sodd,
                )
            )
        pure = (
            len(factors) == 1
            and factors[0][1] == 1
            and components[0].quotient_order == expected_quotient
            and components[0].quotient_odd_part == 1
        )
        if components and components[0].quotient_order != expected_quotient:
            obstructions.append("wrong-prime-domain-quotient-order")
    else:
        expected_torus = 1 << parameter
        split_types: set[int] = set()
        for prime, multiplicity in factors:
            character = jacobi_symbol(12, prime)
            split_types.add(character)
            ambient = prime - character if character in (-1, 1) else prime
            av2, aodd = _v2_odd(ambient)
            if aodd != 1:
                obstructions.append(f"odd-local-torus-order:{prime}:{aodd}")
            source_order = _mersenne_source_unit_order(prime, character, ambient)
            sv2, sodd = _v2_odd(source_order)
            if sodd != 1:
                obstructions.append(f"odd-source-unit-order:{prime}:{sodd}")
            components.append(
                LocalTwoPrimaryComponent(
                    prime,
                    multiplicity,
                    "nonsplit-norm-one-torus"
                    if character == -1
                    else (
                        "split-multiplicative-torus"
                        if character == 1
                        else "ramified-quadratic-algebra"
                    ),
                    character,
                    ambient,
                    av2,
                    aodd,
                    None,
                    None,
                    None,
                    source_order,
                    sv2,
                    sodd,
                )
            )
        if len(split_types) > 1:
            obstructions.append("mixed-split-nonsplit-components")
        pure = (
            len(factors) == 1
            and factors[0][1] == 1
            and components[0].discriminant_character == -1
            and components[0].ambient_order == expected_torus
            and components[0].ambient_odd_part == 1
        )
        if components and components[0].ambient_order != expected_torus:
            obstructions.append("wrong-prime-domain-torus-order")
    return CRTPurityAudit(
        family,
        parameter,
        modulus,
        factors,
        tuple(components),
        pure,
        tuple(dict.fromkeys(obstructions)),
    )


def crt_purity_audits() -> tuple[CRTPurityAudit, ...]:
    return tuple(
        _crt_purity_audit(family, parameter)
        for family, parameter in (
            ("fermat", 4),
            ("fermat", 5),
            ("mersenne", 13),
            ("mersenne", 11),
        )
    )
