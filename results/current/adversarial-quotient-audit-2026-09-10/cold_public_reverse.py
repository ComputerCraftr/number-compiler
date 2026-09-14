"""Fresh public point measurement; exact arithmetic only after timing."""

import json
import sys
from time import perf_counter

from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

steps = int(sys.argv[1])
term = ReverseAddPoweredTerm(196, steps, max_cache_entries=180000)
start = perf_counter()
result = term.digit(0)
seconds = perf_counter() - start
expected = 196
for _ in range(steps):
    expected += int(str(expected)[::-1])
assert result == expected % 10
print(
    json.dumps(
        {
            "steps": steps,
            "result": result,
            "query_seconds": seconds,
            "counters": dict(term._ledger.counters),
        },
        indent=2,
    )
)
