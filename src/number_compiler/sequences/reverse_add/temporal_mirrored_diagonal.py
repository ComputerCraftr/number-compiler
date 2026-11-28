"""Finite Center11 projections over exact reverse/add Q19 transitions."""

from __future__ import annotations

from collections.abc import Callable
from decimal import Decimal

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

from .temporal_center11 import Center11Action
from .temporal_port_quotient import (
    decimal_width_upper_bound,
    native_decimal_string_transport,
)

MAX_MIRRORED_TICKS = 512
# The prior 512-tick envelope for a three-digit seed with one birth per
# tick, expressed as width-weighted work rather than a repetition authority.
CENTER11_WORK_UNITS = 331_264
CENTER11_EXTENDED_SEED_BITS = 256
CENTER11_EXTENDED_SCRATCH_NODES = 10_000


class Center11WorkLimitExceeded(ValueError):
    """The next finite Center11 tick is outside its admitted work envelope."""


def center11_tick_work(width: int) -> int:
    """Charge two decimal passes and the center scan, before their allocation."""
    if type(width) is not int or width < 1:
        raise ValueError("center11 work requires a positive exact width")
    return 2 * width + width // 2 + 1


def center11_scratch_nodes(max_width: int) -> int:
    """Bound simultaneous native strings/operands and fixed matrix/packet work.

    The 24 logical nodes per digit cover current/next/reversed decimal buffers
    and conversion scratch. The fixed allowance covers the simultaneous affine
    matrices and output packet. No endpoint digit lists or cochains are built.
    These are ledger units, not measurements of Python or Decimal heap bytes.
    """
    if type(max_width) is not int or max_width < 1:
        raise ValueError("center11 scratch requires a positive exact width")
    return 24 * max_width + 512


def center11_owned_interval(
    seed: int,
    steps: int,
    max_steps: int | None,
    ledger: ResourceLedger,
    scratch_owner: Callable[[], int],
) -> dict[str, object]:
    """Admit and execute one finite physical interval under its owner's ledger.

    The existing 24-per-digit scratch allowance covers the simultaneously live
    old/new/reversed Decimal coefficients and strings. Width plus one reserves
    their maximum size through a possible birth before each transition.
    """
    if max_steps is not None and type(max_steps) is not int:
        raise ValueError("mirrored diagonal exceeds its finite source interval")
    extended = max_steps is None and steps > MAX_MIRRORED_TICKS
    if extended:
        if (
            seed.bit_length() > CENTER11_EXTENDED_SEED_BITS
            or steps > CENTER11_WORK_UNITS // 3
        ):
            raise Center11WorkLimitExceeded(
                "mirrored diagonal exceeds its finite work envelope"
            )
    elif max_steps is None:
        max_steps = MAX_MIRRORED_TICKS
    if not extended and (
        max_steps is None
        or not 1 <= max_steps <= MAX_MIRRORED_TICKS
        or not 1 <= steps <= max_steps
    ):
        raise ValueError("mirrored diagonal exceeds its finite source interval")
    initial_width = decimal_width_upper_bound(seed)
    scratch = center11_scratch_nodes(initial_width + steps)
    if extended:
        scratch = min(scratch, CENTER11_EXTENDED_SCRATCH_NODES)
        if ledger.max_nodes is not None:
            scratch = min(scratch, max(0, ledger.max_nodes - ledger.nodes))
    if extended and scratch < center11_scratch_nodes(initial_width + 1):
        raise BlockContextBudgetExceeded("center11 scratch exceeds the node budget")
    owner = scratch_owner()
    work = 0

    def tick_started(width: int) -> None:
        nonlocal work
        if extended:
            cost = center11_tick_work(width)
            if cost > CENTER11_WORK_UNITS - work:
                raise Center11WorkLimitExceeded(
                    "mirrored diagonal exceeds its finite work envelope"
                )
            if center11_scratch_nodes(width + 1) > scratch:
                raise BlockContextBudgetExceeded(
                    "center11 scratch exceeds the node budget"
                )
            work += cost
        ledger.bump(_reverse_add_keys.REVERSE_CENTER11_SOURCE_TICKS)

    def coefficient_visits(count: int) -> None:
        ledger.bump(_reverse_add_keys.REVERSE_CENTER11_COEFFICIENT_VISITS, count)

    try:
        with ledger.reservation(owner, nodes=scratch):
            if extended:
                return _center11_interval_packet_source(
                    seed,
                    steps,
                    start_generation=0,
                    on_tick_start=tick_started,
                    on_coefficient_visits=coefficient_visits,
                )
            assert max_steps is not None
            return center11_interval_packet(
                seed,
                steps,
                max_steps=max_steps,
                on_tick_start=tick_started,
                on_coefficient_visits=coefficient_visits,
            )
    except BaseException as error:
        try:
            ledger.bump(_reverse_add_keys.REVERSE_CENTER11_FAILED_WORK)
        except BaseException as accounting_error:
            raise accounting_error from error
        raise


def center11_interval_packet(
    seed: int,
    steps: int,
    *,
    start_generation: int = 0,
    max_steps: int = MAX_MIRRORED_TICKS,
    on_tick_start: Callable[[int], None] | None = None,
    on_coefficient_visits: Callable[[int], None] | None = None,
) -> dict[str, object]:
    """Project one bounded exact source interval into its Center11 action.

    One exact native decimal stream supplies every physical endpoint. Its
    source text supplies the Q19 central coefficient and prefix carry, without
    constructing a second successor or retained carry history. Only current
    decimal buffers and a fixed-size affine action are retained. The packet
    grants no execution ticket or permission to repeat a port program.
    """
    if type(seed) is not int or seed < 0:
        raise ValueError("reverse/add seed must be a nonnegative exact integer")
    if type(max_steps) is not int or not 1 <= max_steps <= MAX_MIRRORED_TICKS:
        raise ValueError("Center11 finite horizon is invalid")
    if type(steps) is not int or not 1 <= steps <= max_steps:
        raise ValueError("Center11 source interval exceeds its finite horizon")
    if type(start_generation) is not int or start_generation < 0:
        raise ValueError("source generation must be nonnegative")

    return _center11_interval_packet_source(
        seed,
        steps,
        start_generation=start_generation,
        on_tick_start=on_tick_start,
        on_coefficient_visits=on_coefficient_visits,
    )


def _center11_interval_packet_source(
    seed: int,
    steps: int,
    *,
    start_generation: int,
    on_tick_start: Callable[[int], None] | None,
    on_coefficient_visits: Callable[[int], None] | None,
) -> dict[str, object]:
    # Decimal's exact integer conversion does not use Python's global int-string
    # digit limit. No full endpoint integer, digit tuple or cochain is retained.
    initial_text = ""
    source_text = ""
    final_text = ""
    try:
        initial_text = str(Decimal(seed))
        source_text = initial_text
        initial_width = len(initial_text)
        initial = _half_residues_from_text(initial_text)
        action = Center11Action.identity(initial_width % 2)
        growth_count = 0
        issued_ticks = 0

        def completed(text: str, _value: Decimal, _reverse: Decimal) -> None:
            nonlocal source_text, action, growth_count, issued_ticks
            try:
                growth = len(text) - len(source_text)
                if growth not in (0, 1):
                    raise AssertionError("native center source lost its width seam")
                center = len(source_text) // 2
                carry = 0
                visits = 0
                try:
                    for index in range(center):
                        coefficient = (
                            ord(source_text[-1 - index]) + ord(source_text[index]) - 96
                        )
                        carry = (coefficient + carry) // 10
                        visits += 1
                    coefficient = (
                        ord(source_text[-1 - center]) + ord(source_text[center]) - 96
                    )
                    visits += 1
                    tick_action = Center11Action.from_physical_ports(
                        source_width=len(source_text),
                        growth=growth,
                        center_coefficient=coefficient,
                        carry_in=carry,
                        carry_out=(coefficient + carry) // 10,
                    )
                finally:
                    if on_coefficient_visits is not None:
                        on_coefficient_visits(visits)
                action = action.then(tick_action)
                growth_count += growth
                issued_ticks += 1
                source_text = text
            except BaseException:
                # The generator traceback can outlive the caller's reservation.
                # Drop its source-sized callback arguments before propagating.
                del text, _value, _reverse
                raise

        final_text, _digit_volume = native_decimal_string_transport(
            initial_text,
            steps,
            max_width=initial_width + steps,
            on_tick_start=on_tick_start,
            on_tick_complete=completed,
        )
        if issued_ticks != steps or source_text != final_text:
            raise AssertionError("native center stream lost its endpoint seam")
        observed = _half_residues_from_text(final_text)
        initial_difference = (initial[0] - initial[1]) % 11
        projected = action.apply(*initial, accumulated=initial_difference)
        if projected[:2] != observed:
            raise AssertionError("Center11 action disagrees with exact Q19 endpoint")
        target_width = len(final_text)
        if target_width != initial_width + growth_count:
            raise AssertionError("Center11 target width disagrees with issued growth")
        center_packet = action.packet(*initial, accumulated=initial_difference)
        center_packet["physical_target_halves"] = list(observed)
        return {
            "source_generation": start_generation,
            "target_generation": start_generation + steps,
            "duration": steps,
            "source_width": initial_width,
            "target_width": target_width,
            "width_growth": growth_count,
            "center11": center_packet,
            "scope": "bounded exact source interval",
            "repetition_authority": "none",
        }
    except BaseException:
        # The enclosing exception frame may be retained by a caller; do not
        # keep source-sized decimal buffers alive after scratch is released.
        initial_text = ""
        source_text = ""
        final_text = ""
        raise


def _half_residues_from_text(text: str) -> tuple[int, int]:
    """Project the two overlapping halves without materializing either word."""
    first = second = 0
    for index in range((len(text) + 1) // 2):
        first = (10 * first + ord(text[index]) - 48) % 11
        second = (10 * second + ord(text[-1 - index]) - 48) % 11
    return first, second


__all__ = ["MAX_MIRRORED_TICKS", "center11_interval_packet", "center11_scratch_nodes"]
