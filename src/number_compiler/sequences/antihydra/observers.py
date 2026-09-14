"""Bounded projections of the source-generated tape and event support."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from math import lcm

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.polynomials.twisted_observer import (
    TwistedCylinderProjection,
)
from number_compiler.sequences.antihydra.blocks import (
    ArithmeticCylinder,
    arithmetic_from_word,
    physical_roof,
)
from number_compiler.sequences.antihydra.machine import EVENT_PRIMES
from number_compiler.sequences.antihydra.projection_fragments import (
    ProjectionFragmentKey,
)
from number_compiler.sequences.antihydra.projection_workspace import (
    SectionImageWorkspace,
)
from number_compiler.sequences.antihydra.runtime import Run
from number_compiler.sequences.antihydra.support import (
    F0,
    STARTUP,
    move,
    section_suffix,
    source_sections,
    sweep,
    tape_intervals,
)


@dataclass(frozen=True, slots=True)
class _BuiltFragment:
    ports: tuple[tuple[int, ...], ...]
    samples: int
    source_h: int
    source_balance: int
    output_h: int
    output_balance: int
    head_delta: int
    time_delta: int


def tape_projection(
    result: Run, width: int, sign: int, modulus: int
) -> TwistedCylinderProjection:
    require_integer(width, "spatial width", 1, 256)
    require_integer(modulus, "coefficient modulus", 2)
    if sign not in (-1, 1):
        raise ValueError("twist must be +/-1")
    values = [0] * width
    period = width * (2 if sign == -1 else 1)
    for lo, hi, prime in tape_intervals(result):
        for offset in range(min(hi - lo, period)):
            x = lo + offset
            turns, slot = divmod(x, width)
            copies = (hi - lo - 1 - offset) // period + 1
            values[slot] += prime * copies * (-1 if sign == -1 and turns & 1 else 1)
    result.ledger.counters["tape_projection_cells"] = (
        result.ledger.counters.get("tape_projection_cells", 0)
        + len(tape_intervals(result)) * period
    )
    return TwistedCylinderProjection(width, sign, tuple(x % modulus for x in values))


class SpaceTimeProjection:
    """Typed event coefficients with prime evaluation and direction augmentation.

    A sweep family is periodic modulo lane phases * coefficient modulus.
    Its quotient is evaluated without enumerating its represented sweep count.
    """

    def __init__(
        self,
        result: Run,
        width: int,
        time_width: int,
        sign: int,
        time_sign: int,
        modulus: int,
        max_terms: int,
        *,
        cache_entries: int = 32,
    ) -> None:
        result.require_source()
        require_integer(width, "spatial width", 1, 64)
        require_integer(time_width, "temporal width", 1, 64)
        require_integer(modulus, "coefficient modulus", 2)
        require_integer(max_terms, "projection work budget", 1)
        require_integer(cache_entries, "section projection cache budget", 0, 32)
        if sign not in (-1, 1) or time_sign not in (-1, 1):
            raise ValueError("twists must be +/-1")
        self.result = result
        self.width, self.time_width = width, time_width
        self.sign, self.time_sign, self.modulus = sign, time_sign, modulus
        self.period = lcm(
            width * (2 if sign == -1 else 1), time_width * (2 if time_sign == -1 else 1)
        )
        self.max_terms = max_terms
        self.work = 0
        self.cache_entries = cache_entries

    def _run(
        self,
        ports: Sequence[list[int]],
        port: int,
        n: int,
        head: int,
        time: int,
        copies: int,
    ) -> tuple[int, int]:
        if n == 0:
            return head, time
        movement = move(port)
        if port == F0:
            n = 1
        count = min(n, self.period)
        if self.work + count > self.max_terms:
            raise ValueError("spacetime projection work budget exceeded")
        self.work += count
        for i in range(count):
            zturn, zslot = divmod(head + movement * i, self.width)
            uturn, uslot = divmod(time + i, self.time_width)
            orientation = (-1 if self.sign == -1 and zturn & 1 else 1) * (
                -1 if self.time_sign == -1 and uturn & 1 else 1
            )
            multiplicity = (n - 1 - i) // self.period + 1
            slot = zslot * self.time_width + uslot
            ports[port][slot] = (
                ports[port][slot] + orientation * multiplicity * copies
            ) % self.modulus
        return (head, time) if port == F0 else (head + movement * n, time + n)

    def _word(
        self,
        ports: Sequence[list[int]],
        word: tuple[tuple[int, int], ...],
        head: int,
        time: int,
        copies: int = 1,
    ) -> tuple[int, int]:
        for port, count in word:
            head, time = self._run(ports, port, count, head, time, copies)
        return head, time

    def _section_key(self, a: int, b: int) -> tuple[int, int]:
        """A demanded image class, never a source or successor identity.

        Sweep images repeat after P*M indices. M repetitions of that cycle
        vanish modulo M, so the family count may be reduced modulo P*M*M.
        Suffix run lengths need only their class modulo P*M. Keep a=0
        distinct: it selects the undefined F0 boundary on odd sections.
        """
        period = self.period * self.modulus
        count = (b // 2 - 1) % (period * self.modulus)
        if count == 0 and not b & 1:
            count += period * self.modulus  # even grammar requires b>=4
        reduced_a = 0 if a == 0 else (a - 1) % period + 1
        return reduced_a, 2 * (count + 1) + (b & 1)

    def _accumulate_section(
        self, ports: list[list[int]], a: int, b: int, head: int, time: int
    ) -> int:
        count = b // 2 - 1
        period = self.period * self.modulus
        samples = min(count, period)
        if samples > self.max_terms - self.work:
            raise ValueError("spacetime sweep refinement budget exceeded")
        for j in range(samples):
            copies = (count - 1 - j) // period + 1
            self._word(ports, sweep(j), head - 2 * j, time + 3 * j * j + 9 * j, copies)
        self._word(
            ports,
            section_suffix(a, b),
            head - 2 * count,
            time + 3 * count * count + 9 * count,
        )
        return samples

    def _section(self, a: int, b: int) -> tuple[tuple[tuple[int, ...], ...], int]:
        ports = [[0] * (self.width * self.time_width) for _ in range(12)]
        samples = self._accumulate_section(ports, a, b, 0, 0)
        return tuple(tuple(row) for row in ports), samples

    def _leaf_fragment(
        self, block: ArithmeticCylinder, h: int, balance: int
    ) -> _BuiltFragment:
        if block.width > 8 or balance + block.minimum < 0:
            raise ValueError(
                "projection leaf requires a safe width-at-most-eight block"
            )
        area = self.width * self.time_width
        ports = [[0] * area for _ in range(12)]
        source_h, source_balance = h, balance
        head = time = samples = 0
        for offset in range(block.width):
            odd = (block.parity_word >> offset) & 1
            if odd != h & 1:
                raise ValueError("projection fragment differs from cylinder support")
            samples += self._accumulate_section(ports, balance, h - 4, head, time)
            leaf = arithmetic_from_word(odd, 1, odd)
            roof = physical_roof(leaf)
            h, balance, left, right = roof.apply(h, balance)
            head += right - left
            time += left + right
            self.result.ledger.bump("spacetime_projection_fragment_leaf_returns")
        expected_h, expected_balance = block.advance(source_h, source_balance)
        if (h, balance) != (expected_h, expected_balance):
            raise ArithmeticError("projection leaf disagrees with arithmetic cylinder")
        return _BuiltFragment(
            tuple(tuple(row) for row in ports),
            samples,
            source_h,
            source_balance,
            h,
            balance,
            head,
            time,
        )

    def _fragment_key(
        self,
        block: ArithmeticCylinder,
        start: int,
        head: int,
        time: int,
    ) -> ProjectionFragmentKey:
        spatial_phase = self.width * (2 if self.sign == -1 else 1)
        temporal_phase = self.time_width * (2 if self.time_sign == -1 else 1)
        return ProjectionFragmentKey(
            self.result._term.segment_owner,
            self.result.requested,
            start,
            (
                block.width,
                block.residue,
                block.output,
                block.delta,
                block.minimum,
                block.parity_word,
            ),
            self.width,
            self.time_width,
            self.sign,
            self.time_sign,
            self.modulus,
            head % spatial_phase,
            time % temporal_phase,
        )

    def _accumulate_retained_fragments(
        self, ports: list[list[int]], capacity: int
    ) -> int:
        """Consume safe source cylinders; a discovered halt stays on the reference path."""
        result = self.result
        if result.halted:
            raise ValueError("halted Antihydra runs require first-failure descent")
        h, balance, head, time, completed = 8, 0, 1, 11, 0
        families = 0
        cache = result._engine.projection_fragments
        for segment in result._term.segments:
            block = segment.cylinder
            if segment.start != completed or block.residue != h % (1 << block.width):
                raise ValueError("retained Antihydra section support was changed")
            if balance + block.minimum < 0:
                raise ValueError(
                    "unsafe Antihydra cylinder requires first-failure descent"
                )
            key = self._fragment_key(block, completed, head, time)
            fragment = cache.get(key)
            if fragment is None:
                from number_compiler.sequences.antihydra.projection_core import (
                    build_projection_fragment,
                )

                fragment = build_projection_fragment(
                    self, key, block, h, balance, capacity
                )
                result.ledger.bump("spacetime_projection_fragment_evaluations")
            self._shift(ports, fragment.typed_ports, head, time)
            result.ledger.bump("spacetime_projection_fragment_translations")
            families += fragment.sampled_sweep_classes
            roof = physical_roof(block)
            h, balance, left, right = roof.apply(h, balance)
            head += right - left
            time += right + left
            completed += block.width
        if (completed, h, balance, head, time) != (
            result.returns,
            result.h,
            result.balance,
            result.head,
            result.physical_ticks,
        ):
            raise ArithmeticError("projection fragments diverged from bound execution")
        return families

    def _shift(
        self,
        ports: list[list[int]],
        image: tuple[tuple[int, ...], ...],
        head: int,
        time: int,
        copies: int = 1,
    ) -> None:
        if not 1 <= copies < self.modulus:
            raise ValueError(
                "section-image multiplicity must be reduced modulo the coefficient modulus"
            )
        area = self.width * self.time_width
        if self.work + 12 * area > self.max_terms:
            raise ValueError("spacetime translation work budget exceeded")
        self.work += 12 * area
        for index in range(area):
            z, u = divmod(index, self.time_width)
            zturn, zslot = divmod(z + head, self.width)
            uturn, uslot = divmod(u + time, self.time_width)
            orientation = (-1 if self.sign == -1 and zturn & 1 else 1) * (
                -1 if self.time_sign == -1 and uturn & 1 else 1
            )
            target = zslot * self.time_width + uslot
            for port in range(12):
                ports[port][target] = (
                    ports[port][target] + orientation * copies * image[port][index]
                ) % self.modulus

    def _flush_section_classes(
        self,
        ports: list[list[int]],
        classes: dict[tuple[tuple[int, int], int, int], int],
        cache: SectionImageWorkspace,
        capacity: int,
    ) -> int:
        """Apply one bounded batch of equal translated section images.

        Section origins are quotient coordinates, not successor identities.
        Combining equal origins is linearity in the requested coefficient
        ring; the chronological source fold and its halt checks remain owned
        by ``source_sections``.
        """
        families = 0
        for (key, head, time), copies in classes.items():
            if copies == 0:
                continue
            image = cache.images.get(key)
            if image is None:
                image, samples = self._section(*key)
                families += samples
                self.result.ledger.bump("spacetime_section_image_evaluations")
                if capacity:
                    cache.put(key, image, capacity)
            else:
                self.result.ledger.bump("spacetime_section_image_hits")
            self._shift(ports, image, head, time, copies)
            self.result.ledger.bump("spacetime_section_translation_batches")
        classes.clear()
        return families

    def evaluate(self) -> dict[str, object]:
        # A projection object can outlive the source validation performed by its
        # constructor.  Re-authenticate at the actual demand boundary before a
        # retained fragment is read or published.
        self.result.require_source()
        self.work = 0
        area = self.width * self.time_width
        ledger = self.result.ledger
        owner = ledger.register("antihydra.spacetime.workspace", "workspace")
        engine = self.result._engine
        if engine.projection_workspace is None:
            engine.projection_workspace = SectionImageWorkspace(ledger)
        cache = engine.projection_workspace
        # Final lanes plus one transient section image and its immutable copy.
        use_images = self.cache_entries > 0 and (
            ledger.max_nodes is None
            or ledger.nodes + 40 * area + self.cache_entries <= ledger.max_nodes
        )
        batch_capacity = self.cache_entries if use_images else 0
        workspace_nodes = (40 if use_images else 16) * area + batch_capacity
        cache.start(area)
        try:
            ledger.reserve(owner, entries=batch_capacity, nodes=workspace_nodes)
        except BaseException:
            cache.clear()
            raise
        # Leave a fixed bound for the scoped source-image tree and its
        # publication seals while one retained root is being constructed.
        fragment_nodes = 24 * area + 3
        available = (
            max(0, (ledger.max_nodes - ledger.nodes - 1024) // fragment_nodes)
            if ledger.max_nodes is not None
            else 32
        )
        capacity = min(self.cache_entries, available)
        try:
            ports = [[0] * area for _ in range(12)]
            self._word(ports, STARTUP, 0, 0)
            if capacity and not self.result.halted:
                families = self._accumulate_retained_fragments(ports, capacity)
            else:
                families = 0
                classes: dict[tuple[tuple[int, int], int, int], int] = {}
                spatial_phase = self.width * (2 if self.sign == -1 else 1)
                temporal_phase = self.time_width * (2 if self.time_sign == -1 else 1)
                for a, b, head, time in source_sections(self.result):
                    if not use_images:
                        families += self._accumulate_section(ports, a, b, head, time)
                        continue
                    key = self._section_key(a, b)
                    translated = key, head % spatial_phase, time % temporal_phase
                    classes[translated] = (
                        classes.get(translated, 0) + 1
                    ) % self.modulus
                    ledger.bump("spacetime_section_class_updates")
                    if len(classes) == batch_capacity:
                        families += self._flush_section_classes(
                            ports, classes, cache, capacity
                        )
                if classes:
                    families += self._flush_section_classes(
                        ports, classes, cache, capacity
                    )

            def channel(direction: int | None, prime: bool) -> list[int]:
                return [
                    sum(
                        ports[p][i] * (EVENT_PRIMES[p] if prime else 1)
                        for p in range(12)
                        if p != F0 and (direction is None or move(p) == direction)
                    )
                    % self.modulus
                    for i in range(area)
                ]

            return {
                "spatial_width": self.width,
                "temporal_width": self.time_width,
                "spatial_sign": self.sign,
                "temporal_sign": self.time_sign,
                "modulus": self.modulus,
                "typed_ports": ports,
                "prime_events": channel(None, True),
                "left_events": channel(-1, False),
                "right_events": channel(1, False),
                "halt": [5 * x % self.modulus for x in ports[F0]],
                "sampled_sweep_classes": families,
            }
        finally:
            ledger.counters["spacetime_projection_terms"] = (
                ledger.counters.get("spacetime_projection_terms", 0) + self.work
            )
            cache.clear()
            ledger.release(owner, entries=batch_capacity, nodes=workspace_nodes)
