"""Check an installed reciprocal cylinder cut crossing the indexed head."""

from __future__ import annotations

import json
import os
from contextlib import redirect_stdout
from importlib.metadata import distribution
from io import StringIO
from unittest.mock import patch

from number_compiler.arithmetic.fields.ordered_matrix import Matrix2
from number_compiler.sequences.antihydra import mahler_cf_reciprocal_tile as tiles


def main() -> None:
    os.environ["NUMBER_COMPILER_ENABLE_CF_RECIPROCAL"] = "1"
    (entry,) = distribution("number-compiler").entry_points.select(
        group="console_scripts", name="number-compiler"
    )
    run = entry.load()
    args = [
        "antihydra",
        "--nth",
        "0",
        "--no-value",
        "--format",
        "json",
        "--info",
        "arithmetic.continued-fraction",
        "--safety-horizon",
        "2048",
    ]

    hits: list[tuple[int, int]] = []
    original = tiles.ReciprocalTile.segment

    def forbidden(*_args: object) -> int:
        raise AssertionError("issued irregular head reopened source digits")

    def segment(tile: tiles.ReciprocalTile, start: int, length: int) -> Matrix2:
        if tile.sealed and tile.first_exponent == 26 and start >= tile.widths[0]:
            assert tile.last_prefixes is not None
            with patch.object(tiles, "reciprocal_row_interval", forbidden):
                result = original(tile, start, length)
            hits.append((start, length))
            return result
        return original(tile, start, length)

    with (
        patch.dict(os.environ, {"NUMBER_COMPILER_ENABLE_CF_CONTINUANT": "0"}),
        redirect_stdout(StringIO()) as portable,
    ):
        assert run(args, shared_cache=False) == 0
    with (
        patch.dict(os.environ, {"NUMBER_COMPILER_ENABLE_CF_CONTINUANT": "1"}),
        patch.object(tiles.ReciprocalTile, "segment", segment),
        redirect_stdout(StringIO()) as native,
    ):
        assert run(args, shared_cache=False) == 0
    assert native.getvalue() == portable.getvalue()
    packet = json.loads(native.getvalue())["info"]["arithmetic.continued-fraction"]
    assert packet["coefficient_count"] == 269
    assert (28, 5) in hits
    print(f"{len(hits)} installed irregular clips before digit production")


if __name__ == "__main__":
    main()
