"""Bidirectional, width-guarded decimal reversal constraint propagation.

This is a *safety constraint* compiler, not an oracle for future digits.
For T(X) = 2*rev10(X), source MSDF digits d[0..w-1] and raw
(w+1)-digit result satisfy

    raw[0] = [d[w-1]>=5]
    raw[w-i] = (2*d[i] + [d[i-1]>=5]) % 10,  i=0..w-1

with zero carry when i=0. The canonical result is obtained by stripping
exactly ``w+1-next_width`` leading zeroes. Every factor is imposed in both
directions: known high source digits force next low digits, known next high
digits restrict the previous low digits and carry, and so on over time.

Each digit is a ten-bit *domain*, not an independently guessed carry.
Modulo constraints use exact forward/backward residue automata. The result
is arc consistency, deliberately NOT an assertion that the remaining domains
represent all globally jointly feasible trajectories. In particular a cycle
of its factors can retain supported values with no simultaneous witness.

Width and any externally observed digits/residues are trusted only as
**supplied authenticated constraints**; this module does not certify an
arbitrary width or border trace by merely finding it consistent.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

_FULL = (1 << 10) - 1
_NONZERO = _FULL ^ 1
_BANDS = {
    "lt_low": frozenset(range(5)),
    "lt_high": frozenset(range(5, 9)),
    "eq": frozenset((9,)),
    "gt_low": frozenset(range(10, 15)),
    "gt_high": frozenset(range(15, 19)),
}


def _members(mask: int) -> tuple[int, ...]:
    return tuple(d for d in range(10) if mask & (1 << d))


def _mask(values: object) -> int:
    if type(values) is int:
        if not 0 <= values <= 9:
            raise ValueError("digit constraint must be between 0 and 9")
        return 1 << values
    if not isinstance(values, (tuple, list, set, frozenset)):
        raise TypeError("digit constraint must be a digit or a collection of digits")
    result = 0
    for digit in values:
        if type(digit) is not int or not 0 <= digit <= 9:
            raise ValueError("digit constraint must be between 0 and 9")
        result |= 1 << digit
    if result == 0:
        raise ValueError("empty digit constraint")
    return result


class InconsistentDigitConstraints(ValueError):
    """An authenticated width, residue or border contradicts a digit factor."""


@dataclass(frozen=True, slots=True)
class InwardSafetySummary:
    widths: tuple[int, ...]
    rounds: int
    known_digit_counts: tuple[int, ...]
    conditional_digit_counts: tuple[int, ...]
    forced_carry_counts: tuple[int, ...]
    # One entry per time row; 0 = RESET0, 1 = RESET1, 2 = conditional.
    carry_vectors: tuple[tuple[int, ...], ...]
    # Raw borrows of rev(X_next) - rev(X_current), LSD-first; 2 means unknown.
    raw_reverse_borrow_vectors: tuple[tuple[int, ...], ...]
    # Domains of symmetric pair sums in the five LT/EQ/GT bands, MSDF side first.
    pair_domains: tuple[tuple[tuple[str, ...], ...], ...]


class InwardCarryConstraints:
    """Finite-horizon, source-guarded bidirectional carry/borrow-safe grammar.

    A width trace is an external input, not generated from residue guesses.
    Source constraints can be single digits, full prefix/suffixes or allowed
    digit domains; an optional residue is checked over the *whole* integer.
    The result retains exact conditional carry domains at every decimal cell.
    """

    def __init__(self, widths: tuple[int, ...], *, max_cells: int = 16384) -> None:
        if (
            type(widths) is not tuple
            or not 1 <= len(widths) <= 513
            or any(type(w) is not int or w <= 0 for w in widths)
            or sum(widths) > max_cells
        ):
            raise ValueError("invalid or over-budget temporal width trace")
        if any(
            not 0 <= widths[t] + 1 - widths[t + 1] <= widths[t]
            for t in range(len(widths) - 1)
        ):
            raise ValueError("successor widths contradict raw reversal/doubling length")
        self.widths = widths
        self._domains: list[list[int]] = [
            [_NONZERO, *([_FULL] * (w - 1))] for w in widths
        ]
        self._residues: dict[tuple[int, int], int] = {}
        self._pair_guards: dict[tuple[int, int], frozenset[str]] = {}
        self._xor_guards: dict[tuple[int, int], int] = {}
        self._borrows: list[list[int]] = [
            [1, *([3] * max(widths[t], widths[t + 1]))] for t in range(len(widths) - 1)
        ]
        self.rounds = 0

    def _shrink(self, time: int, index: int, mask: int) -> bool:
        old = self._domains[time][index]
        current = old & mask
        if not current:
            raise InconsistentDigitConstraints(
                f"empty digit domain at generation {time} position {index}"
            )
        self._domains[time][index] = current
        return current != old

    def constrain(self, time: int, index: int, digits: object) -> None:
        if type(time) is not int or not 0 <= time < len(self.widths):
            raise IndexError("generation outside constraint horizon")
        if type(index) is not int or not 0 <= index < self.widths[time]:
            raise IndexError("digit position outside source width")
        self._shrink(time, index, _mask(digits))

    def constrain_prefix(self, time: int, word: str) -> None:
        if not isinstance(word, str) or not word.isascii() or not word.isdigit():
            raise ValueError("prefix must be decimal digits")
        if len(word) > self.widths[time]:
            raise ValueError("prefix extends beyond source width")
        for i, char in enumerate(word):
            self.constrain(time, i, int(char))

    def constrain_suffix(self, time: int, word: str) -> None:
        if not isinstance(word, str) or not word.isascii() or not word.isdigit():
            raise ValueError("suffix must be decimal digits")
        if len(word) > self.widths[time]:
            raise ValueError("suffix extends beyond source width")
        for i, char in enumerate(word, start=self.widths[time] - len(word)):
            self.constrain(time, i, int(char))

    def constrain_carry(self, time: int, index: int, bit: int) -> None:
        """Apply a proved doubling carry (a digit-threshold guard)."""
        if type(bit) is not int or bit not in (0, 1):
            raise ValueError("carry input must be Boolean")
        self.constrain(time, index, tuple(range(5) if bit == 0 else range(5, 10)))

    def constrain_pair_band(
        self, time: int, index: int, bands: str | tuple[str, ...]
    ) -> None:
        """Join an authenticated five-band LT/EQ/GT pair-output mask."""
        if type(time) is not int or not 0 <= time < len(self.widths):
            raise IndexError(time)
        if type(index) is not int or not 0 <= index < (self.widths[time] + 1) // 2:
            raise IndexError(index)
        requested = frozenset((bands,) if isinstance(bands, str) else bands)
        if not requested or not requested <= _BANDS.keys():
            raise ValueError("invalid LT/EQ/GT band guard")
        key = time, index
        previous = self._pair_guards.get(key, frozenset(_BANDS))
        retained = previous & requested
        if not retained:
            raise InconsistentDigitConstraints("conflicting pair-domain guards")
        self._pair_guards[key] = retained

    def constrain_reflected_xor(self, time: int, index: int, bit: int) -> None:
        """Join an authenticated XOR of the two reflected threshold carries."""
        if type(time) is not int or not 0 <= time < len(self.widths):
            raise IndexError(time)
        if type(index) is not int or not 0 <= index < (self.widths[time] + 1) // 2:
            raise IndexError(index)
        if type(bit) is not int or bit not in (0, 1):
            raise ValueError("XOR mask input must be Boolean")
        key = time, index
        if key in self._xor_guards and self._xor_guards[key] != bit:
            raise InconsistentDigitConstraints("conflicting reflected XOR guards")
        self._xor_guards[key] = bit

    def constrain_residue(self, time: int, modulus: int, residue: int) -> None:
        if type(time) is not int or not 0 <= time < len(self.widths):
            raise IndexError(time)
        if (
            type(modulus) is not int
            or not 2 <= modulus <= 512
            or type(residue) is not int
        ):
            raise ValueError("residue modulus must be in 2..512")
        key = time, modulus
        value = residue % modulus
        previous = self._residues.get(key)
        if previous is not None and previous != value:
            raise InconsistentDigitConstraints("conflicting modular observations")
        self._residues[key] = value

    def constrain_borrow(self, time: int, index: int, bit: int) -> None:
        """Restrict one RAW digit borrow of rev(X_next) - rev(X_current).

        Borrow indices run from 0 (input, always zero) through the maximum
        input-reversal width. This is not a sign-normalized innovation tape.
        """
        if type(time) is not int or not 0 <= time < len(self._borrows):
            raise IndexError(time)
        if type(index) is not int or not 0 <= index < len(self._borrows[time]):
            raise IndexError(index)
        if type(bit) is not int or bit not in (0, 1):
            raise ValueError("borrow input must be Boolean")
        self._borrow_shrink(time, index, 1 << bit)

    def _borrow_shrink(self, time: int, index: int, mask: int) -> bool:
        old = self._borrows[time][index]
        new = old & mask
        if not new:
            raise InconsistentDigitConstraints(
                f"borrow contradiction at generation {time} index {index}"
            )
        self._borrows[time][index] = new
        return new != old

    def borrow(self, time: int, index: int) -> tuple[int, ...]:
        return tuple(bit for bit in (0, 1) if self._borrows[time][index] & (1 << bit))

    def digits(self, time: int, index: int) -> tuple[int, ...]:
        return _members(self._domains[time][index])

    def carry(self, time: int, index: int) -> tuple[int, ...]:
        """Outgoing multiplication carry of one source decimal digit."""
        domain = self.digits(time, index)
        return tuple(sorted({int(d >= 5) for d in domain}))

    def _restrict_triple(
        self,
        t: int,
        current: int,
        previous: int | None,
        target: int | None,
        output_allowed: int,
        *,
        backward: bool,
    ) -> bool:
        row = self._domains[t]
        prev_domain = 1 if previous is None else row[previous]
        cur_domain = row[current]
        output_domain = (
            output_allowed
            if target is None
            else output_allowed & self._domains[t + 1][target]
        )
        prev_keep = 0
        cur_keep = 0
        out_keep = 0
        for a in _members(prev_domain):
            carry = int(a >= 5) if previous is not None else 0
            for b in _members(cur_domain):
                output = (2 * b + carry) % 10
                if output_domain & (1 << output):
                    prev_keep |= 1 << a
                    cur_keep |= 1 << b
                    out_keep |= 1 << output
        if not out_keep:
            raise InconsistentDigitConstraints(
                f"infeasible temporal digit at generation {t}, source cell {current}"
            )
        changed = False
        if backward:
            changed |= self._shrink(t, current, cur_keep)
            if previous is not None:
                changed |= self._shrink(t, previous, prev_keep)
        if target is not None:
            changed |= self._shrink(t + 1, target, out_keep)
        return changed

    def _step(self, t: int, *, backward: bool) -> bool:
        w = self.widths[t]
        nxt = self.widths[t + 1]
        stripped = w + 1 - nxt
        changed = False
        last_mask = self._domains[t][w - 1]
        # raw[0] = h(last input digit): the growth digit of the next word.
        growth_allowed = (1 << 1) if stripped == 0 else (1 << 0)
        if stripped == 0:
            changed |= self._shrink(t + 1, 0, 1 << 1)
        if backward:
            compatible = sum(
                1 << d
                for d in _members(last_mask)
                if growth_allowed & (1 << int(d >= 5))
            )
            changed |= self._shrink(t, w - 1, compatible)
        # For all raw slots, MSDF output cell order is reversed source order.
        for source_i in range(w):
            raw_j = w - source_i
            target_j = raw_j - stripped
            target = target_j if target_j >= 0 else None
            # Discarded digits must be zero; remaining digits equal the target.
            output_allowed = (1 << 0) if target is None else _FULL
            changed |= self._restrict_triple(
                t,
                source_i,
                source_i - 1 if source_i > 0 else None,
                target,
                output_allowed,
                backward=backward,
            )
        return changed

    def _pair_step(self, *, backward: bool) -> bool:
        """Propagate bank five-band and Walsh/XOR witnesses to both digits."""
        if not backward:
            # Forward-only benchmark: do not use a later supplied bank mask
            # to infer earlier source information.
            return False
        changed = False
        for key in sorted(self._pair_guards.keys() | self._xor_guards.keys()):
            t, i = key
            row = self._domains[t]
            j = len(row) - 1 - i
            allowed_bands = self._pair_guards.get(key, frozenset(_BANDS))
            xor_guard = self._xor_guards.get(key)
            left_keep, right_keep = 0, 0
            for a in _members(row[i]):
                for b in (a,) if i == j else _members(row[j]):
                    if not row[j] & (1 << b):
                        continue
                    if xor_guard is not None and int((a >= 5) != (b >= 5)) != xor_guard:
                        continue
                    if not any(a + b in _BANDS[band] for band in allowed_bands):
                        continue
                    left_keep |= 1 << a
                    right_keep |= 1 << b
            changed |= self._shrink(t, i, left_keep)
            if i != j:
                changed |= self._shrink(t, j, right_keep)
        return changed

    def _borrow_step(self, time: int, *, backward: bool) -> bool:
        """Carry-like borrow propagation between the two reversed integers.

        The low digits of rev(X) are just X's leading decimal digits. Thus
        the borrow wire runs from both HIGH source/target borders inward, and
        it may prune their digit domains when a later borrow is authenticated.
        """
        source = self._domains[time]
        target = self._domains[time + 1]
        carry = self._borrows[time]
        changed = False
        for i in range(len(carry) - 1):
            source_domain = source[i] if i < len(source) else 1
            target_domain = target[i] if i < len(target) else 1
            outgoing, incoming_keep, source_keep, target_keep = 0, 0, 0, 0
            for bit in (0, 1):
                if not carry[i] & (1 << bit):
                    continue
                for a in _members(target_domain):
                    for b in _members(source_domain):
                        next_bit = int(a < b + bit)
                        if carry[i + 1] & (1 << next_bit):
                            outgoing |= 1 << next_bit
                            incoming_keep |= 1 << bit
                            source_keep |= 1 << b
                            target_keep |= 1 << a
            if not outgoing:
                raise InconsistentDigitConstraints(
                    f"infeasible reverse-innovation borrow at generation {time} bit {i}"
                )
            changed |= self._borrow_shrink(time, i + 1, outgoing)
            if backward:
                changed |= self._borrow_shrink(time, i, incoming_keep)
                if i < len(source):
                    changed |= self._shrink(time, i, source_keep)
                if i < len(target):
                    changed |= self._shrink(time + 1, i, target_keep)
        return changed

    def _residue_step(self, time: int, modulus: int, residue: int) -> bool:
        row = self._domains[time]
        width = len(row)
        forward: list[set[int]] = [{0}]
        for mask in row:
            forward.append(
                {
                    (10 * r + digit) % modulus
                    for r in forward[-1]
                    for digit in _members(mask)
                }
            )
        if residue not in forward[-1]:
            raise InconsistentDigitConstraints(
                f"generation {time} excludes requested residue modulo {modulus}"
            )
        backward: list[set[int]] = [set() for _ in range(width + 1)]
        backward[width] = {residue}
        for i in range(width - 1, -1, -1):
            digits = _members(row[i])
            continuation = backward[i + 1]
            backward[i] = {
                r
                for r in range(modulus)
                if any((10 * r + digit) % modulus in continuation for digit in digits)
            }
        changed = False
        for i, mask in enumerate(row):
            supported = 0
            for digit in _members(mask):
                if any(
                    (10 * r + digit) % modulus in backward[i + 1] for r in forward[i]
                ):
                    supported |= 1 << digit
            changed |= self._shrink(time, i, supported)
        return changed

    def propagate(
        self,
        *,
        direction: Literal["forward", "both"] = "both",
        max_rounds: int = 256,
    ) -> InwardSafetySummary:
        if direction not in ("forward", "both"):
            raise ValueError("unknown propagation direction")
        if type(max_rounds) is not int or max_rounds < 1:
            raise ValueError("max_rounds must be positive")
        for round_number in range(1, max_rounds + 1):
            changed = False
            for t in range(len(self.widths) - 1):
                changed |= self._step(t, backward=direction == "both")
            # Residue constraints enforce a complete digit-word automaton;
            # backward compatibility can then feed new carry restrictions into
            # preceding and following generations.
            for (t, modulus), residue in sorted(self._residues.items()):
                changed |= self._residue_step(t, modulus, residue)
            changed |= self._pair_step(backward=direction == "both")
            for t in range(len(self._borrows)):
                changed |= self._borrow_step(t, backward=direction == "both")
            if direction == "both":
                for t in range(len(self.widths) - 2, -1, -1):
                    changed |= self._step(t, backward=True)
                    changed |= self._borrow_step(t, backward=True)
            if not changed:
                self.rounds = round_number
                return self.summary()
        raise ValueError("bidirectional safety cone did not stabilize in budget")

    def summary(self) -> InwardSafetySummary:
        carries = tuple(
            tuple(
                0
                if all(d < 5 for d in _members(mask))
                else 1
                if all(d >= 5 for d in _members(mask))
                else 2
                for mask in row
            )
            for row in self._domains
        )
        pairs: list[tuple[tuple[str, ...], ...]] = []
        for t, row in enumerate(self._domains):
            word = []
            for i in range((len(row) + 1) // 2):
                j = len(row) - 1 - i
                key = t, i
                xor_guard = self._xor_guards.get(key)
                allowed = self._pair_guards.get(key, frozenset(_BANDS))
                sums = {
                    a + b
                    for a in _members(row[i])
                    for b in ((a,) if i == j else _members(row[j]))
                    if xor_guard is None or int((a >= 5) != (b >= 5)) == xor_guard
                }
                word.append(
                    tuple(
                        name
                        for name, values in _BANDS.items()
                        if name in allowed and any(s in values for s in sums)
                    )
                )
            pairs.append(tuple(word))
        return InwardSafetySummary(
            self.widths,
            self.rounds,
            tuple(sum(mask.bit_count() == 1 for mask in row) for row in self._domains),
            tuple(sum(mask.bit_count() > 1 for mask in row) for row in self._domains),
            tuple(sum(carry != 2 for carry in row) for row in carries),
            carries,
            tuple(
                tuple(0 if mask == 1 else 1 if mask == 2 else 2 for mask in row[1:])
                for row in self._borrows
            ),
            tuple(pairs),
        )


__all__ = [
    "InconsistentDigitConstraints",
    "InwardCarryConstraints",
    "InwardSafetySummary",
]
