"""Exact finite Collatz actions for sources immediately above a power of two."""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
)
from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)

_ISSUER = object()


@dataclass(frozen=True, slots=True, init=False)
class CollatzTerminalPower2Macro:
    """A source-authenticated normalized action ending exactly at one."""

    source: int
    exponent: int
    physical_ticks: int
    fields: DyadicTerminalFieldAction
    endpoint: int
    width_blank: BlankLedger
    _issuer: object = field(repr=False, compare=False)
    _binding: tuple[object, ...] = field(repr=False, compare=False)

    def __init__(self) -> None:
        raise TypeError("terminal macros require exact power-of-two admission")

    @property
    def normalized_symbols(self) -> int:
        return self.exponent

    @property
    def odd_symbols(self) -> int:
        return 1


def select_terminal_power2_macro(
    source: int, available_physical_ticks: int
) -> CollatzTerminalPower2Macro | None:
    """Admit ``3*source+1=2**e`` only when the whole descent budget fits."""
    if type(source) is not int or source <= 1 or source & 1 == 0:
        return None
    if type(available_physical_ticks) is not int or available_physical_ticks < 0:
        raise ValueError("terminal preimage budget must be a nonnegative integer")
    power = 3 * source + 1
    if power & (power - 1):
        return None
    exponent = power.bit_length() - 1
    physical_ticks = exponent + 1
    if exponent < 2 or physical_ticks > available_physical_ticks:
        return None

    fields = DyadicTerminalFieldAction.one_run(1).then(
        DyadicTerminalFieldAction.zero_run(exponent - 1)
    )
    if fields.steps != exponent or not fields.certifies(source):
        raise AssertionError("power-of-two preimage lost its normalized source guard")
    endpoint = fields.endpoint(source)
    if endpoint != 1:
        raise AssertionError("power-of-two preimage did not descend to one")
    source_width = source.bit_length()
    raw_width = power.bit_length()
    width = BlankLedger(1 - source_width, 1 - source_width, raw_width - source_width)
    macro = object.__new__(CollatzTerminalPower2Macro)
    binding = (source, exponent, physical_ticks, fields, endpoint, width)
    for name, value in zip(
        ("source", "exponent", "physical_ticks", "fields", "endpoint", "width_blank"),
        binding,
        strict=True,
    ):
        object.__setattr__(macro, name, value)
    object.__setattr__(macro, "_issuer", _ISSUER)
    object.__setattr__(macro, "_binding", binding)
    return macro


def _validate_terminal_power2_macro(
    macro: CollatzTerminalPower2Macro,
) -> int:
    """Check the exact word action and return the charged operand-bit count."""
    if (
        type(macro) is not CollatzTerminalPower2Macro
        or getattr(macro, "_issuer", None) is not _ISSUER
    ):
        raise ValueError("terminal preimage macro has no producer authority")
    binding = getattr(macro, "_binding", None)
    if (
        not is_exact_object_tuple(binding)
        or len(binding) != 6
        or binding[0] != macro.source
        or binding[1] != macro.exponent
        or binding[2] != macro.physical_ticks
        or binding[3] is not macro.fields
        or binding[4] != macro.endpoint
        or binding[5] is not macro.width_blank
        or type(macro.source) is not int
        or macro.source <= 1
        or type(macro.exponent) is not int
        or macro.exponent < 2
        or type(macro.physical_ticks) is not int
        or macro.physical_ticks != macro.exponent + 1
        or type(macro.fields) is not DyadicTerminalFieldAction
        or not macro.fields.producer_issued
        or macro.fields.steps != macro.exponent
        or type(macro.endpoint) is not int
        or macro.endpoint != 1
        or type(macro.width_blank) is not BlankLedger
    ):
        raise ValueError("terminal preimage macro payload changed after admission")

    # The equation bounds the exponent by source bit length before allocating
    # its power-of-two denominator.  This also keeps validation bounded when a
    # malformed object carries an enormous exponent.
    source_bits = macro.source.bit_length()
    if macro.exponent > source_bits + 1:
        raise ValueError("terminal preimage macro payload changed after admission")
    power = 1 << macro.exponent
    if 3 * macro.source + 1 != power:
        raise ValueError("terminal preimage macro payload changed after admission")

    # A terminal descent has the exact normalized word 1,0^(e-1).  Its whole
    # emitted field action is fixed, not just its endpoint: joint/F5 consumers
    # also observe the prefix sums and predecessor seam.
    power_minus_one = power - 1
    expected_fields = (
        macro.exponent,
        3,
        1,
        3 * power_minus_one,
        power_minus_one,
        3,
        1,
    )
    actual_fields = (
        macro.fields.steps,
        macro.fields.gain,
        macro.fields.offset,
        macro.fields.sum_gain,
        macro.fields.sum_offset,
        macro.fields.previous_gain,
        macro.fields.previous_offset,
    )
    expected_width = BlankLedger(
        1 - source_bits,
        1 - source_bits,
        power.bit_length() - source_bits,
    )
    if actual_fields != expected_fields or macro.width_blank != expected_width:
        raise ValueError("terminal preimage macro payload changed after admission")

    # Charge the operands actually inspected by the source equation, fixed
    # coefficient calculation, equality checks, and width comparison. The
    # expected coefficient tuple plus the exact power equation entails the
    # endpoint and cylinder guard; rebuilding those from ``field.then`` (or
    # querying the action's modular source residue) would repeat construction.
    return sum(
        max(1, abs(value).bit_length())
        for value in (
            macro.source,
            macro.source,
            power,
            power,
            power_minus_one,
            power_minus_one,
            *actual_fields,
            *expected_fields,
            macro.endpoint,
            *expected_width.as_tuple(),
        )
    )


def validate_terminal_power2_macro(macro: CollatzTerminalPower2Macro) -> None:
    """Check the issued action identity before attaching production consumers."""
    _validate_terminal_power2_macro(macro)


def probe_terminal_power2_macro(
    source: int,
    available_physical_ticks: int,
    *,
    ledger: ResourceLedger,
    scratch: RunArithmeticWorkspace,
    control_bits: int,
) -> CollatzTerminalPower2Macro | None:
    """Preflight and charge the complete terminal classification attempt."""
    if type(source) is not int or source <= 1 or source & 1 == 0:
        raise ValueError("terminal preimage probe requires an odd source above one")
    if type(available_physical_ticks) is not int or available_physical_ticks < 0:
        raise ValueError("terminal preimage budget must be a nonnegative integer")
    if type(control_bits) is not int or control_bits < 1:
        raise ValueError("terminal preimage control width must be positive")
    source_bits = source.bit_length()
    # 3*x+1 < 4*x for x>1, so its exponent is at most source_bits+1.
    scratch.require_bits(16 * (2 * source_bits + control_bits + 12))
    ledger.bump(_collatz_keys.COLLATZ_TERMINAL_POWER2_PROBE_ATTEMPTS)
    ledger.bump(
        _collatz_keys.COLLATZ_TERMINAL_POWER2_PROBE_OPERAND_BITS, 2 * source_bits + 2
    )
    macro = select_terminal_power2_macro(source, available_physical_ticks)
    if macro is None:
        ledger.bump(_collatz_keys.COLLATZ_TERMINAL_POWER2_PROBE_MISSES)
        return None
    validation_operand_bits = _validate_terminal_power2_macro(macro)
    ledger.bump(
        _collatz_keys.COLLATZ_TERMINAL_POWER2_PROBE_VALIDATION_OPERAND_BITS,
        validation_operand_bits,
    )
    return macro


__all__ = [
    "CollatzTerminalPower2Macro",
    "probe_terminal_power2_macro",
    "select_terminal_power2_macro",
    "validate_terminal_power2_macro",
]
