import json
import sys
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from tests.arithmetic.contracts.test_tile_kernel import _runtime

level = int(sys.argv[1])
ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(10))
alphabet = adapter.alphabet(primitive)
source = tiles.leaf(alphabet, 2)
blank = tiles.leaf(alphabet, 19)
for _ in range(level):
    next_source = tiles.join(source.tile, source.tile)
    next_blank = tiles.join(blank.tile, blank.tile)
    source.close()
    blank.close()
    source, blank = next_source, next_blank
padded = tiles.join(source.tile, blank.tile)
source.close()
blank.close()
action = adapter.power(primitive, 4)
engine = CausalTileEngine(scheduler)
width = 1 << level
with padded:
    with engine.output(action, padded.tile) as out:
        points = [tiles.point(out.tile, i) for i in (0, 1, width - 1, width, width + 1)]
        assert points == [7, 14, 14, 7, 19], points
        print(json.dumps({'width':width,'points':points,'counters':dict(ledger.counters)}, indent=2))
