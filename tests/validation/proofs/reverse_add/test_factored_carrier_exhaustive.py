"""All admissible symmetric decimal pair fields through width eight.

The two largest widths are partitioned so each node fits the unchanged
diagnostic guard. These are explicit validation tests, outside the unit gate.
"""

import pytest

from devtools.verification.reverse_factored_carrier import exhaustive


@pytest.mark.parametrize(
    ("width", "first"),
    [(width, None) for width in range(1, 7)]
    + [(width, first) for width in (7, 8) for first in range(19)],
)
def test_factored_successor_all_symmetric_fields(width: int, first: int | None) -> None:
    report = exhaustive(width, first)
    expected = 19 ** (width // 2) * (10 if width % 2 else 1)
    if first is not None:
        expected //= 19
    assert report["complete_partition"]
    assert report["cases"] == expected
