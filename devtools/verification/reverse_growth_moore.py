"""Bounded G161/P7 growth projection audit for the supplied decimal D5 table.

This module is verification-only. Its integer state indices describe the finite
191-state table, not scoped production actions or source occurrences. A P7 word
must be supplied by some other producer; this module does not derive one from a
reverse/add source, publish EXIT continuations, or authorize a temporal cutover.

EXIT and ABSENT are different typed outcomes throughout refinement and weighted
composition. Collapsing them would hide whether a real D5 transition left the
finite chart or the selected Q11 input was unavailable.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass

from devtools.verification import exact_oracle, require_exact_oracle
from devtools.verification._reverse_growth_moore_tables import (
    ABSENT,
    D5_FIELD_TO_MACRO,
    D5_MACRO_PAIRS,
    EXIT,
    SPATIAL_Q11_CLASSES,
    TEMPORAL_OUTPUT_IDS,
    TEMPORAL_T191_CLASSES,
    TEMPORAL_TRANSITIONS,
)
from devtools.verification.reverse_exit_moore import build_d5_return_graph
from number_compiler.projection.output_quotient import canonical_partition_labels


@dataclass(frozen=True, slots=True)
class GrowthAbsent:
    """The selected Q11 continuation is structurally unavailable."""


@dataclass(frozen=True, slots=True)
class GrowthExit:
    """The physical D5 transition returned an active field outside the chart."""


GrowthTerminal = GrowthAbsent | GrowthExit
GrowthTarget = int | GrowthTerminal
ABSENT_RESULT = GrowthAbsent()
EXIT_RESULT = GrowthExit()

_EXPECTED_REFINEMENT = (2, 21, 78, 120, 142, 153, 158, 160, 161, 161)
_EXPECTED_P7_GROUPS = ((0,), (1,), (2,), (3,), (4,), (5,), (6, 7, 8, 9, 10))


def _growth_bit(output_id: int) -> int:
    if type(output_id) is not int or output_id < 0:
        raise ValueError(output_id)
    bit = output_id // 10
    if bit not in (0, 1):
        raise AssertionError("D5 punctured output has a non-Boolean growth sheet")
    return bit


_T191_GROWTH = tuple(_growth_bit(value) for value in TEMPORAL_OUTPUT_IDS)


def _terminal_or_target(code: int, classes: tuple[int, ...]) -> GrowthTarget:
    if code == ABSENT:
        return ABSENT_RESULT
    if code == EXIT:
        return EXIT_RESULT
    if type(code) is not int or code < 0:
        raise ValueError(code)
    _next_spatial, next_temporal = divmod(code, TEMPORAL_T191_CLASSES)
    return classes[next_temporal]


def _refine_growth_states() -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Minimize growth outputs over every Q11 continuation column."""
    classes: list[int] = []
    intern: dict[int, int] = {}
    for growth in _T191_GROWTH:
        if growth not in intern:
            intern[growth] = len(intern)
        classes.append(intern[growth])
    history = [len(intern)]

    while True:
        keys: list[tuple[int, tuple[GrowthTarget, ...]]] = []
        current_classes = tuple(classes)
        for state in range(TEMPORAL_T191_CLASSES):
            row = tuple(
                _terminal_or_target(code, current_classes)
                for code in TEMPORAL_TRANSITIONS[state]
            )
            keys.append((_T191_GROWTH[state], row))
        refined = canonical_partition_labels(keys)
        history.append(len(set(refined)))
        if refined == current_classes:
            return tuple(history), refined
        classes = list(refined)


GROWTH_REFINEMENT_HISTORY, T191_TO_G161 = _refine_growth_states()
if GROWTH_REFINEMENT_HISTORY != _EXPECTED_REFINEMENT:
    raise AssertionError(
        ("D5 growth Moore refinement changed", GROWTH_REFINEMENT_HISTORY)
    )
G161_CLASS_COUNT = 1 + max(T191_TO_G161)
if G161_CLASS_COUNT != 161:
    raise AssertionError(("D5 growth quotient is not G161", G161_CLASS_COUNT))

_G161_MEMBERS = tuple(
    tuple(state for state, class_id in enumerate(T191_TO_G161) if class_id == group)
    for group in range(G161_CLASS_COUNT)
)
G161_OUTPUTS = tuple(_T191_GROWTH[members[0]] for members in _G161_MEMBERS)
if any(
    not members or len({_T191_GROWTH[state] for state in members}) != 1
    for members in _G161_MEMBERS
):
    raise AssertionError("G161 merged distinct current growth outputs")


def _q11_signature(port: int) -> tuple[GrowthTarget, ...]:
    signature: list[GrowthTarget] = []
    for members in _G161_MEMBERS:
        outcomes = {
            _terminal_or_target(TEMPORAL_TRANSITIONS[state][port], T191_TO_G161)
            for state in members
        }
        if len(outcomes) != 1:
            raise AssertionError(("G161 is not right-congruent", port, outcomes))
        signature.append(next(iter(outcomes)))
    return tuple(signature)


_Q11_SIGNATURES = tuple(_q11_signature(port) for port in range(SPATIAL_Q11_CLASSES))
_PORT_INTERN: dict[tuple[GrowthTarget, ...], int] = {}
_Q11_TO_P7: list[int] = []
_P7_Q11_GROUPS: list[list[int]] = []
for _port, _signature in enumerate(_Q11_SIGNATURES):
    _class_id = _PORT_INTERN.get(_signature)
    if _class_id is None:
        _class_id = len(_PORT_INTERN)
        _PORT_INTERN[_signature] = _class_id
        _P7_Q11_GROUPS.append([])
    _Q11_TO_P7.append(_class_id)
    _P7_Q11_GROUPS[_class_id].append(_port)

Q11_TO_P7 = tuple(_Q11_TO_P7)
P7_Q11_GROUPS = tuple(tuple(group) for group in _P7_Q11_GROUPS)
P7_PORT_COUNT = len(P7_Q11_GROUPS)
if P7_Q11_GROUPS != _EXPECTED_P7_GROUPS or P7_PORT_COUNT != 7:
    raise AssertionError(("D5 growth port quotient changed", P7_Q11_GROUPS))

G161_TRANSITIONS: tuple[tuple[GrowthTarget, ...], ...] = tuple(
    tuple(_Q11_SIGNATURES[P7_Q11_GROUPS[p7][0]][state] for p7 in range(P7_PORT_COUNT))
    for state in range(G161_CLASS_COUNT)
)


@dataclass(frozen=True, slots=True)
class GrowthWeight:
    """One finite weighted result before a target state or typed terminal."""

    target: GrowthTarget
    growth: int
    steps: int

    def __post_init__(self) -> None:
        if type(self.growth) is not int or type(self.steps) is not int:
            raise TypeError("growth weights require exact integer counts")
        if self.growth < 0 or self.steps < 0 or self.growth > self.steps:
            raise ValueError("invalid finite growth weight")
        if type(self.target) not in (int, GrowthAbsent, GrowthExit):
            raise TypeError("growth target must be a G161 state or typed terminal")
        if type(self.target) is int and not 0 <= self.target < G161_CLASS_COUNT:
            raise ValueError("growth target is outside G161")


@dataclass(frozen=True, slots=True)
class BoundedGrowthWordAction:
    """Weighted action on all G161 states; no literal P7 word is retained."""

    targets: tuple[GrowthTarget, ...]
    growth: tuple[int, ...]
    steps: tuple[int, ...]

    def __post_init__(self) -> None:
        if not (
            type(self.targets) is tuple
            and type(self.growth) is tuple
            and type(self.steps) is tuple
            and len(self.targets)
            == len(self.growth)
            == len(self.steps)
            == G161_CLASS_COUNT
        ):
            raise ValueError("a bounded growth action requires 161 finite lanes")
        for target, growth, steps in zip(
            self.targets, self.growth, self.steps, strict=True
        ):
            GrowthWeight(target, growth, steps)

    @classmethod
    def identity(cls) -> BoundedGrowthWordAction:
        require_exact_oracle()
        return cls(
            tuple(range(G161_CLASS_COUNT)),
            (0,) * G161_CLASS_COUNT,
            (0,) * G161_CLASS_COUNT,
        )

    @classmethod
    def primitive(cls, p7_port: int) -> BoundedGrowthWordAction:
        require_exact_oracle()
        if type(p7_port) is not int or not 0 <= p7_port < P7_PORT_COUNT:
            raise ValueError("growth continuation must be a P7 column")
        return cls(
            tuple(row[p7_port] for row in G161_TRANSITIONS),
            G161_OUTPUTS,
            (1,) * G161_CLASS_COUNT,
        )

    def then(self, after: BoundedGrowthWordAction) -> BoundedGrowthWordAction:
        require_exact_oracle()
        if type(after) is not BoundedGrowthWordAction:
            raise TypeError("growth actions compose with another bounded action")
        targets: list[GrowthTarget] = []
        weights: list[int] = []
        consumed: list[int] = []
        for state in range(G161_CLASS_COUNT):
            middle = self.targets[state]
            weight = self.growth[state]
            used = self.steps[state]
            if isinstance(middle, (GrowthAbsent, GrowthExit)):
                targets.append(middle)
                weights.append(weight)
                consumed.append(used)
                continue
            if type(middle) is not int:
                raise TypeError("growth target has an unsupported terminal type")
            targets.append(after.targets[middle])
            weights.append(weight + after.growth[middle])
            consumed.append(used + after.steps[middle])
        return BoundedGrowthWordAction(tuple(targets), tuple(weights), tuple(consumed))

    def square(self) -> BoundedGrowthWordAction:
        return self.then(self)

    def power(self, exponent: int) -> BoundedGrowthWordAction:
        require_exact_oracle()
        if type(exponent) is not int or exponent < 0:
            raise ValueError("growth action exponent must be a natural number")
        result = BoundedGrowthWordAction.identity()
        factor = self
        value = exponent
        while value:
            if value & 1:
                result = result.then(factor)
            value >>= 1
            if value:
                factor = factor.square()
        return result

    def at(self, state: int) -> GrowthWeight:
        require_exact_oracle()
        if type(state) is not int or not 0 <= state < G161_CLASS_COUNT:
            raise ValueError("growth state index is outside the finite audit table")
        return GrowthWeight(self.targets[state], self.growth[state], self.steps[state])


def growth_action_for_p7_word(word: tuple[int, ...]) -> BoundedGrowthWordAction:
    """Compile a caller-supplied finite P7 word; no source schedule is inferred."""
    require_exact_oracle()
    if type(word) is not tuple:
        raise TypeError("growth audit word must be a tuple")
    result = BoundedGrowthWordAction.identity()
    for port in word:
        result = result.then(BoundedGrowthWordAction.primitive(port))
    return result


@dataclass(frozen=True, slots=True)
class D5GrowthProjectionAudit:
    source_fields: int
    growth_rows: int
    no_growth_rows: int
    projected_successors: int
    exit_rows: int
    absent_columns: int
    production_admission: bool = False


def audit_d5_growth_projection() -> D5GrowthProjectionAudit:
    """Compare every physical D5 row with its bounded literal successor."""
    require_exact_oracle()
    graph = build_d5_return_graph()
    if len(D5_FIELD_TO_MACRO) != len(graph.sources):
        raise AssertionError("generated D5 index differs from the literal field order")
    field_ids = {field: index for index, field in enumerate(graph.sources)}
    growth_rows = no_growth_rows = exits = projected = 0
    for index, (field, target_index) in enumerate(
        zip(graph.sources, graph.successors, strict=True)
    ):
        macro = D5_FIELD_TO_MACRO[index]
        spatial, temporal = D5_MACRO_PAIRS[macro]
        state = T191_TO_G161[temporal]
        p7 = Q11_TO_P7[spatial]
        target = (
            graph.sources[target_index]
            if target_index < len(graph.sources)
            else graph.exit_payloads[target_index - len(graph.sources)]
        )
        growth = len(target) - len(field)
        if growth not in (0, 1):
            raise AssertionError(("D5 row has non-Boolean growth", field, target))
        if G161_OUTPUTS[state] != growth:
            raise AssertionError(
                ("G161 output disagrees with literal successor", field, target)
            )
        transition = G161_TRANSITIONS[state][p7]
        if len(target) == len(field) + 1:
            exits += 1
            growth_rows += 1
            if type(transition) is not GrowthExit:
                raise AssertionError(("physical D5 EXIT was lost", field, transition))
        else:
            no_growth_rows += 1
            next_index = field_ids.get(target)
            if next_index is None:
                raise AssertionError(
                    ("D5 no-growth successor left the chart", field, target)
                )
            next_macro = D5_FIELD_TO_MACRO[next_index]
            _next_spatial, next_temporal = D5_MACRO_PAIRS[next_macro]
            expected = T191_TO_G161[next_temporal]
            if transition != expected:
                raise AssertionError(
                    ("G161 successor disagrees with literal row", field, target)
                )
        projected += 1

    absent_columns = sum(
        type(target) is GrowthAbsent for row in G161_TRANSITIONS for target in row
    )
    if not any(
        type(target) is GrowthExit for row in G161_TRANSITIONS for target in row
    ):
        raise AssertionError("G161 table lost every EXIT")
    if absent_columns == 0:
        raise AssertionError("G161 table lost every ABSENT continuation")
    return D5GrowthProjectionAudit(
        len(graph.sources),
        growth_rows,
        no_growth_rows,
        projected,
        exits,
        absent_columns,
    )


def audit_growth_moore() -> dict[str, object]:
    require_exact_oracle()
    return {
        "temporal_source_classes": TEMPORAL_T191_CLASSES,
        "growth_classes": G161_CLASS_COUNT,
        "growth_refinement_history": GROWTH_REFINEMENT_HISTORY,
        "q11_ports": SPATIAL_Q11_CLASSES,
        "growth_ports": P7_PORT_COUNT,
        "q11_to_p7": Q11_TO_P7,
        "p7_q11_groups": P7_Q11_GROUPS,
        "typed_exit_absent": True,
        "source_selected_schedule": False,
        "production_admission": False,
    }


if __name__ == "__main__":
    with exact_oracle():
        print(asdict(audit_d5_growth_projection()))
