"""Installed source-issued relative-return action checks."""

from __future__ import annotations

from typing import Any


def installed_supplied_period_checks_each_oriented_word_once() -> None:
    import json
    from contextlib import redirect_stdout
    from io import StringIO
    from unittest.mock import patch

    from number_compiler.api.cli import main
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.double_reverse import protected_temporal_bank as bank

    work: dict[str, int] = {}
    bump = ResourceLedger.bump

    def count(self: ResourceLedger, key: str, amount: int = 1) -> None:
        work[key] = work.get(key, 0) + amount
        bump(self, key, amount)

    for motif, admitted in [
        ("0332966666667", True),
        ("0" + "3" * 60 + "29" + "6" * 64 + "7", True),
        ("0123456789012", False),
    ]:
        work.clear()

        buf = StringIO()
        with (
            patch.object(ResourceLedger, "bump", count),
            redirect_stdout(buf),
            patch.object(
                bank, "advance_periodic_state", side_effect=AssertionError("replay")
            ),
        ):
            rc = main(
                [
                    "2rev10",
                    "--seed",
                    "17" + motif * (1800 // len(motif)) + "88",
                    "--nth",
                    "576",
                    "--max-state-bits",
                    "16384",
                    "--no-value",
                    "--info",
                    "temporal.grammar",
                    "--temporal-grammar-position",
                    "350",
                    "--temporal-grammar-period",
                    str(len(motif)),
                    "--format",
                    "json",
                ],
                shared_cache=False,
            )
        packet = json.loads(buf.getvalue())["info"]["temporal.grammar"]
        assert rc == (0 if admitted else 3)
        assert packet["status"] == ("available" if admitted else "unavailable")
        prefix = "double_reverse_periodic_bank_"
        assert work[prefix + "relative_checks"] == len(motif) * (1 if admitted else 3)
        assert work.get(prefix + "relative_actions", 0) == int(admitted)
        assert work.get(prefix + "temporal_states", 0) == 0
        if admitted:
            assert packet["f_steps"] == 288 and packet["motif"] == []


def installed_five_fibre_work_and_short_fallback() -> None:
    import io
    import json
    from contextlib import redirect_stdout
    from importlib import import_module
    from unittest.mock import patch

    from number_compiler.api.cli import main

    native: Any = import_module("number_compiler.kernels._reverse_quotients")

    source = "17" + "1" * 1800 + "88"
    kernel = native.multiply
    counters: list[Any] = []

    def measured(*args: object) -> object:
        digits, work = kernel(*args)
        counters.append(work)
        return digits, work

    for ticks in (144, 16):
        counters.clear()
        output = io.StringIO()
        with patch.object(native, "multiply", measured), redirect_stdout(output):
            status = main(
                [
                    "5rev10",
                    "--seed",
                    source,
                    "--nth",
                    str(ticks),
                    "--max-steps",
                    str(ticks),
                    "--max-state-bits",
                    "8192",
                    "--max-output-bits",
                    "8192",
                    "--format",
                    "json",
                ],
                shared_cache=False,
            )
        value = int(source)
        for _ in range(ticks):
            value = 5 * int(str(value)[::-1])
        assert status == 0 and int(json.loads(output.getvalue())["value"]) == value
        if ticks == 144:
            assert len(counters) == 1
            assert counters[0][0] < 5092 and counters[0][1] < 2061, counters
        else:
            assert not counters


def run_task(task: str) -> None:
    tasks = {
        "installed_supplied_period_checks_each_oriented_word_once": installed_supplied_period_checks_each_oriented_word_once,
        "installed_five_fibre_work_and_short_fallback": installed_five_fibre_work_and_short_fallback,
    }
    tasks[task]()
