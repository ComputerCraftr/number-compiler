import json
from dataclasses import asdict
from time import perf_counter
from unittest.mock import patch

from devtools.experiments.power_numbers.square_consumer_congruence import (
    terminal_deck_congruence_audits,
)
from number_compiler.api.cli import _render_value
from number_compiler.api.number_api import NumberCompiler
from number_compiler.arithmetic.carry.decimal_jet_cylinder import DecimalCarryJetBlock
from number_compiler.arithmetic.polynomials.primary_jet import PrimaryJetBlock

# Compare the old per-width power operation against the table on the same widths.
widths = tuple(range(1024))
atom = PrimaryJetBlock.digit(0, degree=5, modulus=32)
blocks = tuple(
    DecimalCarryJetBlock(w, DecimalCarryJetBlock.identity().cylinder) for w in widths
)
start = perf_counter()
old = tuple(atom.power_block(w).power for w in widths)
old_seconds = perf_counter() - start
start = perf_counter()
new = tuple(b.clock for b in blocks)
new_seconds = perf_counter() - start
assert old == new
rows = []
for family, index, kwargs in [
    ("196", 8, {}),
    ("collatz", 8, {"seed": 27}),
    ("fermat", 14, {}),
    ("mersenne", 16384, {}),
]:
    term = NumberCompiler().project_nth(family, index, **kwargs)
    calls = {"materialize": 0, "width": 0}
    payload = term.payload
    owner = type(payload.term) if hasattr(payload, "term") else type(payload)
    original_materialize = owner.materialize

    def observed_materialize(
        self, *args, _calls=calls, _original=original_materialize, **kw
    ):
        _calls["materialize"] += 1
        return _original(self, *args, **kw)

    with patch.object(owner, "materialize", observed_materialize):
        if hasattr(owner, "width"):
            original_width = owner.width

            def observed_width(
                self, *args, _calls=calls, _original=original_width, **kw
            ):
                _calls["width"] += 1
                return _original(self, *args, **kw)

            with patch.object(owner, "width", observed_width):
                text = _render_value(
                    term, output_base=10 if family == "196" else 16, max_bits=20000
                )
        else:
            text = _render_value(term, output_base=16, max_bits=20000)
    value = int(text, 10 if family == "196" else 16)
    if family == "196":
        expected = 196
        for _ in range(index):
            expected += int(str(expected)[::-1])
    elif family == "collatz":
        expected = 27
        for _ in range(index):
            expected = 3 * expected + 1 if expected % 2 else expected // 2
    else:
        expected = (1 << (1 << index)) + 1 if family == "fermat" else (1 << index) - 1
    assert value == expected
    rows.append(
        {
            "family": family,
            "index": index,
            "output_base": 10 if family == "196" else 16,
            "characters": len(text),
            **calls,
        }
    )
print(
    json.dumps(
        {
            "clock": {
                "width_requests": len(widths),
                "old_power_calls": len(widths),
                "new_power_calls": 0,
                "fixed_table_phases": 128,
                "old_seconds": old_seconds,
                "new_seconds": new_seconds,
                "scope": "clock lookup only, table import excluded; not end-to-end speedup",
            },
            "cli": rows,
            "terminal_decks": [asdict(r) for r in terminal_deck_congruence_audits()],
        },
        indent=2,
    )
)
