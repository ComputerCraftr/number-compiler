"""Four-phase 2rev10 center return and *conditional* temporal Moore selector.

The even-width center pair u,v passes through three odd-width middle digits
before the next even-width pair.  Every external carry is represented by a
source-derived Boolean port; the final right-side neighbor is an F5 port.

A periodic center driver makes the resulting finite return-map model genuinely
periodic, but does NOT certify that any actual source supplies that driver
indefinitely.  No observed 2/3 multiplier word is promoted to source authority.
"""

from __future__ import annotations

from dataclasses import dataclass


def _h(value: int) -> int:
    return int(value >= 5)


@dataclass(frozen=True, slots=True)
class CenterDriver:
    """External center-seam response across one four-generation width cycle.

    left_1/2/3 are threshold carries from the left neighbors of the three
    odd center stages; right_f5 is the right neighbor residue at stage three.
    The right neighbor's threshold is NOT needed to determine the next center
    pair, but must be kept separately if that neighbor itself is observed.
    """

    left_1: int
    left_2: int
    left_3: int
    right_f5: int

    def __post_init__(self) -> None:
        if (
            any(
                type(v) is not int or v not in (0, 1)
                for v in (
                    self.left_1,
                    self.left_2,
                    self.left_3,
                )
            )
            or type(self.right_f5) is not int
            or not 0 <= self.right_f5 < 5
        ):
            raise ValueError("center driver requires three carry bits and one F5 digit")


@dataclass(frozen=True, slots=True)
class CenterReturn:
    """Exact even-pair -> three odd centers -> next even-pair action."""

    initial: tuple[int, int]
    driver: CenterDriver
    odd: tuple[int, int, int]
    next_pair: tuple[int, int]

    @property
    def forced_carries(self) -> tuple[int, int, int]:
        """Incoming carries recovered from the parities of output digits."""
        return self.odd[1] & 1, self.odd[2] & 1, self.next_pair[1] & 1

    @property
    def next_sum_band(self) -> int:
        """Five-way symmetric pair band: LTlow, LThigh, EQ, GTlow, GThigh."""
        s = sum(self.next_pair)
        if s <= 4:
            return 0
        if s <= 8:
            return 1
        if s == 9:
            return 2
        if s <= 14:
            return 3
        return 4

    @property
    def output_f5(self) -> tuple[int, int]:
        return self.next_pair[0] % 5, self.next_pair[1] % 5


def center_return(pair: tuple[int, int], driver: CenterDriver) -> CenterReturn:
    """Evaluate the entire four-step center block without scanning the halves.

    Each external carry has already been supplied as a conditional port.  The
    caller must prove its real source/guard when publishing source predictions.
    """
    if (
        type(pair) is not tuple
        or len(pair) != 2
        or any(type(v) is not int or not 0 <= v < 10 for v in pair)
        or not isinstance(driver, CenterDriver)
    ):
        raise ValueError("center return requires an ordered two-digit pair and driver")
    u, v = pair
    b1 = (2 * v + _h(u)) % 10
    b2 = (2 * b1 + driver.left_1) % 10
    b3 = (2 * b2 + driver.left_2) % 10
    next_pair = (
        (2 * driver.right_f5 + _h(b3)) % 10,
        (2 * b3 + driver.left_3) % 10,
    )
    result = CenterReturn(pair, driver, (b1, b2, b3), next_pair)
    if result.forced_carries != (
        driver.left_1,
        driver.left_2,
        driver.left_3,
    ):
        raise AssertionError("center parity/carry seam equality failed")
    return result


@dataclass(frozen=True, slots=True)
class CenterMooreResult:
    """Complete finite conditional driver quotient, not a real-source theorem."""

    input_period: int
    all_states: int
    pointed_preperiod: int
    pointed_state_period: int
    pointed_return_multiplier: int
    state_periods: tuple[int, ...]
    multiplier_moore_classes: int
    band_moore_classes: int
    digit_moore_classes: int
    multiplier_class_by_state: tuple[int, ...]
    multiplier_class_successors: tuple[int, ...]


def _moore_labels(
    outputs: tuple[object, ...],
    successors: tuple[int, ...],
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Coarsest complete-future equivalence for one deterministic output port."""
    n = len(outputs)
    alphabet = {key: i for i, key in enumerate(dict.fromkeys(outputs))}
    part = tuple(alphabet[x] for x in outputs)
    while True:
        signatures = tuple((outputs[i], part[successors[i]]) for i in range(n))
        classes = {key: i for i, key in enumerate(dict.fromkeys(signatures))}
        refined = tuple(classes[x] for x in signatures)
        if len(set(refined)) == len(set(part)):
            part = refined
            break
        part = refined
    target: dict[int, int] = {}
    for i, c in enumerate(part):
        next_c = part[successors[i]]
        if c in target and target[c] != next_c:
            raise AssertionError("not a future-closed Moore quotient")
        target[c] = next_c
    return part, tuple(target[i] for i in range(len(target)))


def _eventual_periods(successors: tuple[int, ...]) -> tuple[int, ...]:
    """Find the full-state cycle length reached from every conditional state."""
    n = len(successors)
    result = [0] * n
    for origin in range(n):
        if result[origin]:
            continue
        path: list[int] = []
        local: dict[int, int] = {}
        at = origin
        while result[at] == 0 and at not in local:
            local[at] = len(path)
            path.append(at)
            at = successors[at]
        period = result[at] if result[at] else len(path) - local[at]
        for v in path:
            result[v] = period
    return tuple(result)


def conditional_center_moore(
    start: tuple[int, int],
    motif: tuple[CenterDriver, ...],
    *,
    max_states: int = 10000,
) -> CenterMooreResult:
    """Moore-minimize a declared periodic center forcing program.

    Enumerates *all* 100 center pairs and all inlet phases, so periods are
    calculated by the transition graph rather than fitted to one observed
    point.  The forcing motif is a model assumption, not a source certificate.
    """
    if not motif or any(not isinstance(v, CenterDriver) for v in motif):
        raise ValueError("center Moore requires a nonempty typed inlet motif")
    if len(motif) * 100 > max_states:
        raise ValueError("center Moore state budget exceeded")
    center_return(start, motif[0])  # input validation
    period = len(motif)

    # Stable dense indexing: state=(u,v,driver_phase).
    def index(u: int, v: int, phase: int) -> int:
        return (phase * 10 + u) * 10 + v

    successors: list[int] = []
    bank_outputs: list[tuple[int, ...]] = []
    digit_outputs: list[tuple[int, ...]] = []
    phases: list[int] = []
    for p in range(period):
        for u in range(10):
            for v in range(10):
                result = center_return((u, v), motif[p])
                a, b = result.next_pair
                successors.append(index(a, b, (p + 1) % period))
                phases.append(p)
                bank_outputs.append(
                    (
                        p,
                        result.next_sum_band,
                        *result.output_f5,
                        _h(a),
                        _h(b),
                        int(_h(a) != _h(b)),
                        *result.forced_carries,
                    )
                )
                digit_outputs.append((p, u, v))
    next_indices = tuple(successors)
    full_periods = _eventual_periods(next_indices)
    if any(p % period for p in full_periods):
        raise AssertionError("closed center orbit lost inlet phase")
    multiplier_outputs = tuple(
        (phases[i], full_periods[i] // period) for i in range(len(next_indices))
    )
    multiplier_classes, multiplier_transitions = _moore_labels(
        multiplier_outputs,
        next_indices,
    )
    band_classes, _ = _moore_labels(tuple(bank_outputs), next_indices)
    digit_classes, _ = _moore_labels(tuple(digit_outputs), next_indices)

    at = index(start[0], start[1], 0)
    seen: dict[int, int] = {}
    ticks = 0
    while at not in seen:
        seen[at] = ticks
        at = next_indices[at]
        ticks += 1
    entry = seen[at]
    return CenterMooreResult(
        period,
        len(next_indices),
        entry,
        ticks - entry,
        (ticks - entry) // period,
        full_periods,
        len(set(multiplier_classes)),
        len(set(band_classes)),
        len(set(digit_classes)),
        multiplier_classes,
        multiplier_transitions,
    )


@dataclass(frozen=True, slots=True)
class CenterInputMoore:
    """Source-independent future quotient for *all* 40 carry/F5 input letters.

    No input word is generated here; a source-authorized producer must still
    supply its letters.  These classes are valid for every possible input
    sequence because the transition partition is fully input-driven.
    """

    contract: str
    state_count: int
    moore_classes: int
    refinement_rounds: int
    driver_alphabet: tuple[CenterDriver, ...]
    classes_by_pair: tuple[int, ...]
    transitions: tuple[tuple[int, ...], ...]
    labels: tuple[tuple[int, ...], ...]

    def class_for(self, pair: tuple[int, int]) -> int:
        center_return(pair, self.driver_alphabet[0])  # validate
        return self.classes_by_pair[pair[0] * 10 + pair[1]]


def center_input_moore(contract: str = "band") -> CenterInputMoore:
    """Exact Moore refinement of the 100 center-pair states under all inputs.

    Labels are current-state observations.  For instance `band` retains only
    the five GT/EQ/LT classes, `band_f5_xor` retains the pair band, sum mod 5
    and threshold carry XOR, and `complete` retains both literal digits.
    Future refinement automatically retains needed hidden digit distinctions.
    """
    valid = {
        "band",
        "f5",
        "xor",
        "band_xor",
        "band_f5",
        "band_f5_xor",
        "complete",
    }
    if contract not in valid:
        raise ValueError("unknown center input-driven observation contract")
    letters = tuple(
        CenterDriver(a, b, c, residue)
        for a in (0, 1)
        for b in (0, 1)
        for c in (0, 1)
        for residue in range(5)
    )
    states = tuple((u, v) for u in range(10) for v in range(10))

    def label(pair: tuple[int, int]) -> tuple[int, ...]:
        u, v = pair
        total = u + v
        band = (
            0
            if total <= 4
            else 1
            if total <= 8
            else 2
            if total == 9
            else 3
            if total <= 14
            else 4
        )
        residue = total % 5
        xor = int(_h(u) != _h(v))
        return {
            "band": (band,),
            "f5": (residue,),
            "xor": (xor,),
            "band_xor": (band, xor),
            "band_f5": (band, residue),
            "band_f5_xor": (band, residue, xor),
            "complete": (u, v),
        }[contract]

    observations = tuple(label(s) for s in states)

    def next_index(state: tuple[int, int], driver: CenterDriver) -> int:
        a, b = center_return(state, driver).next_pair
        return 10 * a + b

    raw_next = tuple(
        tuple(next_index(state, driver) for driver in letters) for state in states
    )
    classes = {v: i for i, v in enumerate(dict.fromkeys(observations))}
    partition = tuple(classes[v] for v in observations)
    rounds = 0
    while True:
        signature = tuple(
            (observations[i], tuple(partition[v] for v in raw_next[i]))
            for i in range(100)
        )
        next_classes = {v: i for i, v in enumerate(dict.fromkeys(signature))}
        refined = tuple(next_classes[v] for v in signature)
        rounds += 1
        if len(next_classes) == len(set(partition)):
            partition = refined
            break
        if rounds > 100:
            raise AssertionError(
                "center input-driven Moore refinement did not stabilize"
            )
        partition = refined
    nclasses = len(set(partition))
    transitions: list[tuple[int, ...] | None] = [None] * nclasses
    labels: list[tuple[int, ...] | None] = [None] * nclasses
    for i, c in enumerate(partition):
        row = tuple(partition[s] for s in raw_next[i])
        if transitions[c] is None:
            transitions[c] = row
            labels[c] = observations[i]
        elif transitions[c] != row or labels[c] != observations[i]:
            raise AssertionError("center quotient is not future-closed")
    if any(row is None for row in transitions) or any(x is None for x in labels):
        raise AssertionError("center quotient contains an empty class")
    return CenterInputMoore(
        contract,
        100,
        nclasses,
        rounds,
        letters,
        partition,
        tuple(x for x in transitions if x is not None),
        tuple(x for x in labels if x is not None),
    )


def encode_multiplier_word(multipliers: tuple[int, ...]) -> str:
    """Encode observed exact multiplier events: 3 -> 1, 2 -> 0.

    This is a *finite* proposed selector word.  An input multiplier other
    than 2 or 3 must be reported, never coerced into that alphabet.
    """
    if any(type(m) is not int or m not in (2, 3) for m in multipliers):
        raise ValueError("binary selector has only the multiplier alphabet {2, 3}")
    return "".join("1" if m == 3 else "0" for m in multipliers)


__all__ = [
    "CenterDriver",
    "CenterInputMoore",
    "CenterMooreResult",
    "CenterReturn",
    "center_input_moore",
    "center_return",
    "conditional_center_moore",
    "encode_multiplier_word",
]
