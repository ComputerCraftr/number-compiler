"""Exact reverse oracle tests explicitly opt into whole-field construction."""

from collections.abc import Iterator

import pytest

from devtools.proofs import exact_oracle


@pytest.fixture(autouse=True)
def exact_reverse_oracle_scope() -> Iterator[None]:
    with exact_oracle():
        yield
