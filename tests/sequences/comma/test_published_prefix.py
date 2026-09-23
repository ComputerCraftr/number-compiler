"""The external table is an independent fixture, not a production branch oracle."""

from hashlib import sha256
from pathlib import Path

from number_compiler.sequences.comma.power import CommaTerm


def test_complete_published_table_matches_independent_literal_children() -> None:
    path = Path(__file__).parents[2] / "support" / "oeis" / "b367620.txt"
    raw = path.read_bytes()
    assert sha256(raw).hexdigest() == (
        "6b905a1bd72888bfef1bbea65d75c286a0a07e5652f3365a6bddd4a1f1011a5b"
    )
    rows = [tuple(map(int, row.split())) for row in raw.decode().splitlines()]
    value = 20
    for expected_index, (index, expected_value) in enumerate(rows, 1):
        assert index == expected_index
        assert value == expected_value
        if index in (1, 4, 16, 32, 64, 128, 256, 512, 1024, 20000):
            assert CommaTerm(index).materialize() == value
        children = [
            value + 10 * (value % 10) + leading
            for leading in range(1, 10)
            if str(value + 10 * (value % 10) + leading)[0] == str(leading)
        ]
        assert len(children) == 1
        value = children[0]
    assert len(rows) == 20000
