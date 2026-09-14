"""Pinned literal six-state reference semantics; undefined F0 takes no step.

The bounded reference retains the current tape, never an event history. Production
macro execution uses the same transition alphabet through the section grammar.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from hashlib import sha256

MACHINE = "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"
MACHINE_SHA256 = sha256(MACHINE.encode("ascii")).hexdigest()
EVENT_PRIMES = (31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79)
# write, displacement, target; None is the undefined F0 port.
TRANSITIONS: tuple[tuple[tuple[int, int, int] | None, ...], ...] = (
    ((1, 1, 1), (1, 1, 0)),
    ((0, -1, 2), (1, -1, 4)),
    ((1, -1, 3), (1, -1, 2)),
    ((1, -1, 0), (0, -1, 1)),
    ((1, -1, 5), (1, 1, 4)),
    (None, (0, 1, 0)),
)


@dataclass(frozen=True, slots=True)
class Event:
    state: int
    read: int
    head: int
    time: int

    @property
    def port(self) -> int:
        return 2 * self.state + self.read

    @property
    def prime(self) -> int:
        return EVENT_PRIMES[self.port]


@dataclass(slots=True)
class LiteralMachine:
    """Independent bounded oracle, including explicitly visited blank cells."""

    state: int = 0
    initial_head: int = 0
    left: int = 0
    right: int = 0
    visited_min: int = 0
    visited_max: int = 0
    ones: set[int] = field(default_factory=set)
    halted: bool = False

    @property
    def head(self) -> int:
        return self.initial_head + self.right - self.left

    @property
    def time(self) -> int:
        return self.left + self.right

    def step(self) -> Event | None:
        if self.halted:
            return None
        head = self.head
        read = int(head in self.ones)
        event = Event(self.state, read, head, self.time)
        transition = TRANSITIONS[self.state][read]
        if transition is None:
            self.halted = True
            return None
        write, move, self.state = transition
        if write:
            self.ones.add(head)
        else:
            self.ones.discard(head)
        self.left += int(move < 0)
        self.right += int(move > 0)
        self.visited_min = min(self.visited_min, self.head)
        self.visited_max = max(self.visited_max, self.head)
        return event

    @classmethod
    def section(cls, a: int, b: int) -> LiteralMachine:
        if type(a) is not int or type(b) is not int or a < 0 or b < 2:
            raise ValueError("section requires a>=0 and b>=2")
        return cls(
            state=4,
            initial_head=b + 1,
            visited_min=-a,
            visited_max=b + 1,
            ones=set(range(-a, 0)) | set(range(1, b + 1)),
        )
