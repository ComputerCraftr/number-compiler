"""Reverse-engineer the missing Fermat/Mersenne source certificate.

This research module treats the old exhaustive/factor-backed source classes only
as a truth oracle.  It searches for a small candidate-derived arithmetic SLP
whose output has the *local* support semantics required by production:

* output == 0 (mod q) on a passing local Frobenius/Kummer component;
* output != 0 (mod q) on a failing component.

Local-axis testing is intentionally stronger than matching the candidate-global
gcd: it prevents two bad components from cancelling into an apparently good
scalar.  Candidate programs are built from the production-safe
:mod:`devtools.verification.special_source_program` language and contain no factor,
CRT, recurrence, carrier, polynomial-expansion, or deferred-exponent token.

Agreement on bounded controls is not a theorem.  The final report distinguishes
"bounded CEGIS fit" from "proved source constructor" and never promotes the
former into production.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

from devtools.experiments.power_numbers.terminal_frobenius_chunk import (
    special_local_frobenius_chunk_audit,
)
from devtools.verification.special_source_program import (
    FoldedSupportInstruction,
    FoldedSupportProgram,
    SpecialSourceCertificateCandidate,
)
from number_compiler.sequences.power_numbers.frobenius_chunk import (
    SpecialFrobeniusChunkSpec,
)
from number_compiler.sequences.power_numbers.numbers import (
    fermat_number,
    mersenne_number,
)
from number_compiler.sequences.power_numbers.terminal_threshold import (
    prime_decision_chunk_spec,
    terminal_threshold_spec,
)

# Research truth only.  Prime controls use the candidate itself as the sole
# local factor; composite controls use complete factorizations only to label
# expected local support.  None of this table is imported by production.
_FERMAT_FACTORS: dict[int, tuple[int, ...]] = {
    4: (65537,),
    5: (641, 6700417),
    6: (274177, 67280421310721),
    7: (59649589127497217, 5704689200685129054721),
}
_FERMAT_LOCAL_WITNESSES: dict[int, tuple[int, ...]] = {
    **_FERMAT_FACTORS,
    # F9 is not used as a complete candidate factorization.  These independently
    # verified divisors have different ambient v2(q-1) depths (16 and 11), which
    # is exactly the adversary needed to prevent the CEGIS search from learning
    # the accidental F5/F6/F7 "every composite factor stops at n+2" pattern.
    9: (
        2424833,
        7455602825647884208337395736200454918783366342657,
    ),
}

_MERSENNE_FACTORS: dict[int, tuple[int, ...]] = {
    11: (23, 89),
    13: (8191,),
    17: (131071,),
    19: (524287,),
    23: (47, 178481),
    29: (233, 1103, 2089),
    31: (2147483647,),
    37: (223, 616318177),
    43: (431, 9719, 2099863),
    47: (2351, 4513, 13264529),
    61: (2305843009213693951,),
}

# The CEGIS basis deliberately excludes arbitrary integer constants and generic
# exponentiation.  Every atom is derived canonically from family/parameter/chunk.
_CEGIS_ATOMS = (
    "zero",
    "one",
    "neg_one",
    "parameter",
    "start_level",
    "span",
    "baseline_v2",
    "base_stride_v2",
    "required_v2",
    "modulus_bits",
    "trace_seed",
    "factor_stride",
    "base_stride",
    "required_stride",
    "folded_half_degree",
    "sparse_root",
)


@dataclass(frozen=True, slots=True)
class FoldedSupportLocalControl:
    family: str
    parameter: int
    spec: SpecialFrobeniusChunkSpec
    prime_factor: int
    expected_pass: bool
    source: str

    @property
    def modulus(self) -> int:
        return (
            fermat_number(self.parameter)
            if self.family == "fermat"
            else mersenne_number(self.parameter)
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            self.family,
            self.parameter,
            self.spec.start_level,
            self.spec.span,
            self.prime_factor,
            self.expected_pass,
        )


@dataclass(frozen=True, slots=True)
class SourceCertificateControlSummary:
    family: str
    candidate_controls: int
    local_axes: int
    passing_axes: int
    failing_axes: int
    split_candidate_chunks: int


@dataclass(frozen=True, slots=True)
class _SynthExpr:
    op: str
    atom: str | None = None
    left: _SynthExpr | None = None
    right: _SynthExpr | None = None

    @property
    def key(self) -> tuple[object, ...]:
        completed: dict[int, tuple[object, ...]] = {}
        pending: list[tuple[_SynthExpr, bool]] = [(self, False)]
        while pending:
            node, ready = pending.pop()
            if id(node) in completed:
                continue
            if node.op == "atom":
                completed[id(node)] = ("atom", node.atom)
                continue
            if not ready:
                _push_synth_children(pending, node)
                continue
            left = completed[id(node.left)] if node.left is not None else None
            completed[id(node)] = (
                (node.op, left)
                if node.right is None
                else (node.op, left, completed[id(node.right)])
            )
        return completed[id(self)]

    def render(self) -> str:
        completed: dict[int, str] = {}
        pending: list[tuple[_SynthExpr, bool]] = [(self, False)]
        while pending:
            node, ready = pending.pop()
            if id(node) in completed:
                continue
            if node.op == "atom":
                completed[id(node)] = str(node.atom)
                continue
            if not ready:
                _push_synth_children(pending, node)
                continue
            assert node.left is not None
            left = completed[id(node.left)]
            if node.op == "neg":
                completed[id(node)] = f"(-{left})"
            elif node.op == "square":
                completed[id(node)] = f"sq({left})"
            else:
                assert node.right is not None
                symbol = {"add": "+", "sub": "-", "mul": "*"}[node.op]
                completed[id(node)] = f"({left}{symbol}{completed[id(node.right)]})"
        return completed[id(self)]

    def atoms(self) -> frozenset[str]:
        found: set[str] = set()
        seen: set[int] = set()
        pending: list[_SynthExpr] = [self]
        while pending:
            node = pending.pop()
            if id(node) in seen:
                continue
            seen.add(id(node))
            if node.op == "atom":
                found.add(str(node.atom))
            else:
                for child in (node.left, node.right):
                    if child is not None:
                        pending.append(child)
        return frozenset(found)


def _push_synth_children(
    pending: list[tuple[_SynthExpr, bool]], node: _SynthExpr
) -> None:
    pending.append((node, True))
    for child in (node.right, node.left):
        if child is not None:
            pending.append((child, False))


@dataclass(frozen=True, slots=True)
class FoldedSupportCEGISResult:
    family: str
    controls: int
    max_operator_cost: int
    exhaustive_cost_reached: int
    semantic_states_examined: int
    search_state_cap: int
    found: bool
    expression: str | None
    operator_cost: int | None
    train_mismatches: int | None
    holdout_mismatches: int | None
    local_support_exact_on_all_controls: bool
    theorem_proved: bool
    rejection_reason: str
    program: FoldedSupportProgram | None = None


@dataclass(frozen=True, slots=True)
class FoldedSupportBeamResult:
    family: str
    max_operator_cost: int
    beam_width: int
    best_operator_cost: int
    best_expression: str
    train_mismatches: int
    holdout_mismatches: int
    all_control_mismatches: int
    bounded_fit: bool
    theorem_proved: bool = False


@dataclass(frozen=True, slots=True)
class SpecialSourceCertificateResearchReport:
    fermat_controls: SourceCertificateControlSummary
    mersenne_controls: SourceCertificateControlSummary
    fermat_cegis: FoldedSupportCEGISResult
    mersenne_cegis: FoldedSupportCEGISResult
    fermat_beam: FoldedSupportBeamResult
    mersenne_beam: FoldedSupportBeamResult
    prime_decision_candidates_checked: int
    factor_truth_only: bool
    production_promoted: bool
    source_program_language_has_deferred_power: bool
    source_program_language_has_factor_input: bool
    conclusion: str


def _factor_table(family: str) -> dict[int, tuple[int, ...]]:
    """Complete factorizations used only for candidate-global differentials."""
    if family == "fermat":
        return _FERMAT_FACTORS
    if family == "mersenne":
        return _MERSENNE_FACTORS
    raise ValueError(family)


def _local_factor_witnesses(family: str) -> dict[int, tuple[int, ...]]:
    """Divisor witnesses sufficient for local-axis CEGIS controls."""
    if family == "fermat":
        return _FERMAT_LOCAL_WITNESSES
    if family == "mersenne":
        return _MERSENNE_FACTORS
    raise ValueError(family)


def _candidate_modulus(family: str, parameter: int) -> int:
    return (
        fermat_number(parameter) if family == "fermat" else mersenne_number(parameter)
    )


def _validate_factor_table() -> None:
    for family in ("fermat", "mersenne"):
        complete = _factor_table(family)
        for parameter, factors in _local_factor_witnesses(family).items():
            modulus = _candidate_modulus(family, parameter)
            product = 1
            for factor in factors:
                if factor <= 2 or modulus % factor:
                    raise AssertionError((family, parameter, factor))
                product *= factor
            if parameter in complete and product != modulus:
                raise AssertionError((family, parameter, product, modulus))


def _chunk_specs_for_candidate(
    family: str, parameter: int
) -> tuple[SpecialFrobeniusChunkSpec, ...]:
    terminal = terminal_threshold_spec(family, parameter)
    specs: dict[tuple[int, int], SpecialFrobeniusChunkSpec] = {}
    # Exercise both small conditional chunks and the actual prime-decision chunk.
    max_start = min(5, max(1, terminal.terminal_level))
    for start in range(1, max_start + 1):
        remaining = terminal.terminal_level - start + 1
        if remaining <= 0:
            break
        for span in range(1, min(4, remaining) + 1):
            spec = SpecialFrobeniusChunkSpec(
                family,
                parameter,
                start,
                span,
                terminal.baseline_local_v2,
                terminal.modulus_bits,
            )
            specs[(start, span)] = spec
    if terminal.prime_decision_level > 0:
        spec = prime_decision_chunk_spec(terminal)
        specs[(spec.start_level, spec.span)] = spec
    return tuple(specs[key] for key in sorted(specs))


def folded_support_local_controls(family: str) -> tuple[FoldedSupportLocalControl, ...]:
    _validate_factor_table()
    out: list[FoldedSupportLocalControl] = []
    for parameter, factors in sorted(_local_factor_witnesses(family).items()):
        for spec in _chunk_specs_for_candidate(family, parameter):
            for factor in factors:
                audit = special_local_frobenius_chunk_audit(
                    family,
                    parameter,
                    spec.start_level,
                    spec.span,
                    factor,
                )
                out.append(
                    FoldedSupportLocalControl(
                        family,
                        parameter,
                        spec,
                        factor,
                        audit.all_levels_pass,
                        "factor-backed-local-folded-support-truth",
                    )
                )
    return tuple(out)


def control_summary(family: str) -> SourceCertificateControlSummary:
    controls = folded_support_local_controls(family)
    candidate_keys = {(c.parameter, c.spec.start_level, c.spec.span) for c in controls}
    split = 0
    for key in candidate_keys:
        rows = [
            c.expected_pass
            for c in controls
            if (c.parameter, c.spec.start_level, c.spec.span) == key
        ]
        if any(rows) and not all(rows):
            split += 1
    return SourceCertificateControlSummary(
        family,
        len(candidate_keys),
        len(controls),
        sum(c.expected_pass for c in controls),
        sum(not c.expected_pass for c in controls),
        split,
    )


def _program_from_expr(expr: _SynthExpr) -> FoldedSupportProgram:
    instructions: list[FoldedSupportInstruction] = []
    memo: dict[tuple[object, ...], int] = {}

    stack: list[tuple[_SynthExpr, bool]] = [(expr, False)]
    while stack:
        node, expanded = stack.pop()
        if node.key in memo:
            continue
        children = tuple(
            child for child in (node.left, node.right) if child is not None
        )
        if children and not expanded:
            stack.append((node, True))
            for child in reversed(children):
                if child.key not in memo:
                    stack.append((child, False))
            continue
        if node.op == "atom":
            ins = FoldedSupportInstruction("atom", str(node.atom))
        elif node.op in ("neg", "square"):
            assert node.left is not None
            ins = FoldedSupportInstruction(node.op, memo[node.left.key])
        else:
            assert node.left is not None and node.right is not None
            ins = FoldedSupportInstruction(
                node.op, memo[node.left.key], memo[node.right.key]
            )
        index = len(instructions)
        instructions.append(ins)
        memo[node.key] = index
    return FoldedSupportProgram(tuple(instructions))


def _atom_vectors(
    controls: tuple[FoldedSupportLocalControl, ...],
    *,
    global_values: bool = False,
) -> dict[tuple[int, ...], _SynthExpr]:
    vectors: dict[tuple[int, ...], _SynthExpr] = {}
    for name in _CEGIS_ATOMS:
        program = FoldedSupportProgram.atom(name)
        cache: dict[tuple[object, ...], int] = {}
        row: list[int] = []
        for control in controls:
            key = control.spec.canonical_key
            value = cache.get(key)
            if value is None:
                value = program.evaluate(control.spec).value
                cache[key] = value
            row.append(
                value % (control.modulus if global_values else control.prime_factor)
            )
        vectors.setdefault(tuple(row), _SynthExpr("atom", atom=name))
    return vectors


def _local_mismatches(
    vector: tuple[int, ...],
    controls: tuple[FoldedSupportLocalControl, ...],
) -> int:
    return sum(
        (value % control.prime_factor == 0) != control.expected_pass
        for value, control in zip(vector, controls)
    )


def _combine_vector(
    op: str,
    left: tuple[int, ...],
    right: tuple[int, ...] | None,
    controls: tuple[FoldedSupportLocalControl, ...],
    *,
    global_values: bool = False,
) -> tuple[int, ...]:
    def modulus(c: FoldedSupportLocalControl) -> int:
        return c.modulus if global_values else c.prime_factor

    if op == "neg":
        return tuple((-a) % modulus(c) for a, c in zip(left, controls))
    if op == "square":
        return tuple((a * a) % modulus(c) for a, c in zip(left, controls))
    if op == "gcd_n":
        if not global_values:
            raise ValueError("gcd_n requires candidate-global semantic vectors")
        return tuple(gcd(a, c.modulus) % c.modulus for a, c in zip(left, controls))
    if right is None:
        raise ValueError(op)
    if op == "add":
        return tuple((a + b) % modulus(c) for a, b, c in zip(left, right, controls))
    if op == "sub":
        return tuple((a - b) % modulus(c) for a, b, c in zip(left, right, controls))
    if op == "mul":
        return tuple((a * b) % modulus(c) for a, b, c in zip(left, right, controls))
    raise ValueError(op)


def _pick_train_holdout(
    controls: tuple[FoldedSupportLocalControl, ...],
) -> tuple[
    tuple[FoldedSupportLocalControl, ...], tuple[FoldedSupportLocalControl, ...]
]:
    # Hold out the largest parameter and every third chunk of the preceding one.
    max_parameter = max(c.parameter for c in controls)
    train: list[FoldedSupportLocalControl] = []
    holdout: list[FoldedSupportLocalControl] = []
    for index, control in enumerate(controls):
        if control.parameter == max_parameter or (
            control.parameter == max_parameter - 1 and index % 3 == 0
        ):
            holdout.append(control)
        else:
            train.append(control)
    if not train or not holdout:
        raise AssertionError((len(train), len(holdout)))
    return tuple(train), tuple(holdout)


def _evaluate_program_locally(
    program: FoldedSupportProgram,
    controls: tuple[FoldedSupportLocalControl, ...],
) -> int:
    cache: dict[tuple[object, ...], int] = {}
    mismatches = 0
    for control in controls:
        key = control.spec.canonical_key
        value = cache.get(key)
        if value is None:
            value = program.evaluate(control.spec).value
            cache[key] = value
        actual_pass = value % control.prime_factor == 0
        mismatches += actual_pass != control.expected_pass
    return mismatches


def synthesize_folded_support_program(
    family: str,
    *,
    max_operator_cost: int = 3,
    state_cap: int = 120_000,
    allow_internal_gcd: bool = False,
) -> FoldedSupportCEGISResult:
    """Search the bounded arithmetic grammar by local semantic vectors.

    The search is exhaustive until ``state_cap`` is exceeded.  When a candidate
    fits the training axes it is always checked on held-out axes.  Even a perfect
    bounded fit remains ``theorem_proved=False`` until an independent symbolic
    derivation exists.
    """
    family = str(family)
    max_operator_cost = int(max_operator_cost)
    state_cap = int(state_cap)
    if max_operator_cost < 0 or state_cap < 100:
        raise ValueError((max_operator_cost, state_cap))
    all_controls = folded_support_local_controls(family)
    train, holdout = _pick_train_holdout(all_controls)
    global_values = bool(allow_internal_gcd)
    by_cost: list[dict[tuple[int, ...], _SynthExpr]] = [
        _atom_vectors(train, global_values=global_values)
    ]
    seen: dict[tuple[int, ...], tuple[int, _SynthExpr]] = {
        vector: (0, expr) for vector, expr in by_cost[0].items()
    }
    examined = len(seen)
    exhaustive_cost = 0

    def maybe_result(
        cost: int, vector: tuple[int, ...], expr: _SynthExpr
    ) -> None | FoldedSupportCEGISResult:
        if _local_mismatches(vector, train) != 0:
            return None
        program = _program_from_expr(expr)
        train_miss = _evaluate_program_locally(program, train)
        holdout_miss = _evaluate_program_locally(program, holdout)
        all_miss = _evaluate_program_locally(program, all_controls)
        # A bounded fit is evidence for the search, not a proof.  In particular
        # Fermat has only one presently known nontrivial prime candidate in this
        # parameter range, so empirical separation can overfit metadata.
        reason = (
            "bounded semantic fit only; no symbolic candidate->folded-support identity proved"
            if all_miss == 0
            else "training fit rejected by held-out local axes"
        )
        return FoldedSupportCEGISResult(
            family,
            len(all_controls),
            max_operator_cost,
            exhaustive_cost,
            examined,
            state_cap,
            True,
            expr.render(),
            cost,
            train_miss,
            holdout_miss,
            all_miss == 0,
            False,
            reason,
            program,
        )

    for vector, expr in by_cost[0].items():
        result = maybe_result(0, vector, expr)
        if result is not None:
            return result

    for cost in range(1, max_operator_cost + 1):
        current: dict[tuple[int, ...], _SynthExpr] = {}
        prior = by_cost[cost - 1]
        for vector, expr in prior.items():
            unary_ops = (
                ("neg", "square", "gcd_n") if allow_internal_gcd else ("neg", "square")
            )
            for op in unary_ops:
                out = _combine_vector(
                    op, vector, None, train, global_values=global_values
                )
                current.setdefault(out, _SynthExpr(op, left=expr))
        for left_cost in range(cost):
            right_cost = cost - 1 - left_cost
            left_map = by_cost[left_cost]
            right_map = by_cost[right_cost]
            for lv, le in left_map.items():
                for rv, re in right_map.items():
                    for op in ("add", "sub", "mul"):
                        out = _combine_vector(
                            op, lv, rv, train, global_values=global_values
                        )
                        current.setdefault(out, _SynthExpr(op, left=le, right=re))
                    if len(current) + len(seen) > state_cap:
                        return FoldedSupportCEGISResult(
                            family,
                            len(all_controls),
                            max_operator_cost,
                            exhaustive_cost,
                            examined,
                            state_cap,
                            False,
                            None,
                            None,
                            None,
                            None,
                            False,
                            False,
                            "semantic state cap reached before next operator-cost layer closed",
                            None,
                        )
        current = {
            vector: expr for vector, expr in current.items() if vector not in seen
        }
        by_cost.append(current)
        for vector, expr in current.items():
            seen[vector] = (cost, expr)
        examined = len(seen)
        exhaustive_cost = cost
        for vector, expr in current.items():
            result = maybe_result(cost, vector, expr)
            if result is not None:
                return result

    return FoldedSupportCEGISResult(
        family,
        len(all_controls),
        max_operator_cost,
        exhaustive_cost,
        examined,
        state_cap,
        False,
        None,
        None,
        None,
        None,
        False,
        False,
        "no local-support-exact program in the exhaustively searched arithmetic grammar",
        None,
    )


def beam_search_folded_support_program(
    family: str,
    *,
    max_operator_cost: int = 4,
    beam_width: int = 200,
) -> FoldedSupportBeamResult:
    """Heuristic deeper search used only after the exhaustive small grammar.

    This does not change the proof status.  It asks whether a slightly deeper
    arithmetic expression even *empirically* tracks the local support axes.
    The beam is ranked by training-axis mismatches, then expression size.
    """
    family = str(family)
    max_operator_cost = int(max_operator_cost)
    beam_width = int(beam_width)
    if max_operator_cost < 1 or beam_width < 1:
        raise ValueError((max_operator_cost, beam_width))
    controls = folded_support_local_controls(family)
    train, holdout = _pick_train_holdout(controls)
    base = _atom_vectors(train)
    beam = dict(base)
    best_vector, best_expr = min(
        beam.items(),
        key=lambda item: (
            _local_mismatches(item[0], train),
            len(item[1].render()),
            item[1].render(),
        ),
    )
    best_cost = 0
    for cost in range(1, max_operator_cost + 1):
        candidates: dict[tuple[int, ...], _SynthExpr] = {}
        pool = dict(base)
        pool.update(beam)
        for vector, expr in beam.items():
            for op in ("neg", "square"):
                out = _combine_vector(op, vector, None, train)
                candidates.setdefault(out, _SynthExpr(op, left=expr))
            for right_vector, right_expr in pool.items():
                for op in ("add", "sub", "mul"):
                    out = _combine_vector(op, vector, right_vector, train)
                    candidates.setdefault(
                        out, _SynthExpr(op, left=expr, right=right_expr)
                    )
        ranked = sorted(
            candidates.items(),
            key=lambda item: (
                _local_mismatches(item[0], train),
                len(item[1].render()),
                item[1].render(),
            ),
        )
        if not ranked:
            break
        candidate_vector, candidate_expr = ranked[0]
        candidate_loss = _local_mismatches(candidate_vector, train)
        best_loss = _local_mismatches(best_vector, train)
        if candidate_loss < best_loss or (
            candidate_loss == best_loss
            and len(candidate_expr.render()) < len(best_expr.render())
        ):
            best_vector, best_expr, best_cost = candidate_vector, candidate_expr, cost
        if candidate_loss == 0:
            best_vector, best_expr, best_cost = candidate_vector, candidate_expr, cost
            break
        beam = dict(ranked[:beam_width])

    program = _program_from_expr(best_expr)
    train_miss = _evaluate_program_locally(program, train)
    holdout_miss = _evaluate_program_locally(program, holdout)
    all_miss = _evaluate_program_locally(program, controls)
    return FoldedSupportBeamResult(
        family,
        max_operator_cost,
        beam_width,
        best_cost,
        best_expr.render(),
        train_miss,
        holdout_miss,
        all_miss,
        all_miss == 0,
        False,
    )


def candidate_certificate_differential(
    family: str,
    parameter: int,
    program: FoldedSupportProgram,
) -> tuple[SpecialSourceCertificateCandidate, int, bool]:
    """Compare one proposed source certificate with factor-backed prime-decision truth."""
    terminal = terminal_threshold_spec(family, parameter)
    if terminal.prime_decision_level <= 0:
        raise ValueError((family, parameter, "no unresolved chunk"))
    spec = prime_decision_chunk_spec(terminal)
    candidate = SpecialSourceCertificateCandidate.evaluate(
        spec,
        program,
        method="research-folded-support-program",
    )
    factors = _factor_table(family)[parameter]
    expected_pass: list[int] = []
    for factor_1 in factors:
        audit = special_local_frobenius_chunk_audit(
            family,
            parameter,
            spec.start_level,
            spec.span,
            factor_1,
        )
        if audit.all_levels_pass:
            expected_pass.append(factor_1)
    expected_support = 1
    for factor_2 in expected_pass:
        expected_support *= factor_2
    return candidate, expected_support, candidate.support_gcd == expected_support


def source_certificate_research_report() -> SpecialSourceCertificateResearchReport:
    # Cost two is exhaustively closed.  Cost three already exceeds the bounded
    # semantic-state budget, so a small deterministic beam probes the next layer
    # without pretending that it is an exhaustive proof.
    fermat = synthesize_folded_support_program(
        "fermat", max_operator_cost=2, state_cap=250_000, allow_internal_gcd=True
    )
    mersenne = synthesize_folded_support_program(
        "mersenne", max_operator_cost=2, state_cap=250_000, allow_internal_gcd=True
    )
    fermat_beam = beam_search_folded_support_program(
        "fermat", max_operator_cost=3, beam_width=60
    )
    mersenne_beam = beam_search_folded_support_program(
        "mersenne", max_operator_cost=3, beam_width=60
    )
    prime_decision_checked = 0
    for family, result in (("fermat", fermat), ("mersenne", mersenne)):
        if result.program is None or not result.local_support_exact_on_all_controls:
            continue
        for parameter in _factor_table(family):
            terminal = terminal_threshold_spec(family, parameter)
            if terminal.prime_decision_level <= 0:
                continue
            candidate_certificate_differential(family, parameter, result.program)
            prime_decision_checked += 1
    return SpecialSourceCertificateResearchReport(
        control_summary("fermat"),
        control_summary("mersenne"),
        fermat,
        mersenne,
        fermat_beam,
        mersenne_beam,
        prime_decision_checked,
        True,
        False,
        False,
        False,
        "source-certificate architecture closed; bounded CEGIS cannot promote without a symbolic folded-support identity",
    )
