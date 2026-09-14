import json
import time

from number_compiler.arithmetic.polynomials.twisted_observer import (
    first_mirror_obstruction,
)
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

for generation in (8, 16):
    outputs = []
    for route in ("points", "dag"):
        term = ReverseAddPoweredTerm(196, generation)
        start = time.perf_counter()
        result = (
            first_mirror_obstruction(term.width(), term.digit)
            if route == "points"
            else term.mirror_obstruction()
        )
        seconds = time.perf_counter() - start
        outputs.append(result)
        print(
            json.dumps(
                {
                    "generation": generation,
                    "route": route,
                    "seconds": seconds,
                    "coefficients": None if result is None else result.coefficients,
                    "work": {
                        k: v
                        for k, v in term._ledger.counters.items()
                        if k.startswith(
                            ("point_response_", "tile_cylinder_", "tile_causal_action_")
                        )
                    },
                    "peak_nodes": term._ledger.peak_nodes,
                    "retained_nodes": term._ledger.nodes,
                }
            ),
            flush=True,
        )
    assert outputs[0] == outputs[1]
