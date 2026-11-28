"""Check installed reciprocal cylinder cuts through issued row actions."""

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
    args_prefix = [
        "antihydra",
        "--nth",
        "0",
        "--no-value",
        "--format",
        "json",
        "--info",
        "arithmetic.continued-fraction",
        "--safety-horizon",
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

    opens: list[tuple[int, int, int]] = []
    raw_interval = tiles.reciprocal_row_interval

    def row_interval(q: int, row: int, width: int, start: int, count: int) -> int:
        assert (row, start, count) == (2, 0, 1)
        opens.append((row, start, count))
        return raw_interval(q, row, width, start, count)

    def boundary_segment(
        tile: tiles.ReciprocalTile, start: int, length: int
    ) -> Matrix2:
        if tile.sealed and tile.first_exponent == 34 and (start, length) == (0, 50):
            assert tile.widths == (24, 25, 26, 26) and len(tile.row_prefixes) == 4
            with patch.object(tiles, "reciprocal_row_interval", row_interval):
                return original(tile, start, length)
        return original(tile, start, length)

    for horizon, count, check in ((2048, 269, segment), (3584, 471, boundary_segment)):
        args = [*args_prefix, str(horizon)]
        with (
            patch.dict(os.environ, {"NUMBER_COMPILER_ENABLE_CF_CONTINUANT": "0"}),
            redirect_stdout(StringIO()) as portable,
        ):
            assert run(args, shared_cache=False) == 0
        with (
            patch.dict(os.environ, {"NUMBER_COMPILER_ENABLE_CF_CONTINUANT": "1"}),
            patch.object(tiles.ReciprocalTile, "segment", check),
            redirect_stdout(StringIO()) as native,
        ):
            assert run(args, shared_cache=False) == 0
        assert native.getvalue() == portable.getvalue()
        packet = json.loads(native.getvalue())["info"]["arithmetic.continued-fraction"]
        assert packet["coefficient_count"] == count
    assert (28, 5) in hits
    assert opens == [(2, 0, 1)]
    print(f"{len(hits)} installed irregular clips and 2 reused complete rows")


if __name__ == "__main__":
    main()
