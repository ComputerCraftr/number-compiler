"""Shared point observers do not manufacture a lowering capability."""

import pytest

from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.assertions import forbid_explicit_lowering


@pytest.mark.parametrize("family", ("reverse-add", "collatz"))
def test_public_point_never_creates_lowering_capability(
    monkeypatch: pytest.MonkeyPatch, family: str
) -> None:
    import number_compiler.hashlife.observation.hashlife_projection as projection

    term = (
        ReverseAddPoweredTerm(196, 4)
        if family == "reverse-add"
        else PoweredCollatzTerm(54, 8)
    )
    monkeypatch.setattr(projection, "LoweringCapability", forbid_explicit_lowering)
    assert term.width() > 0
    assert term.digit(0) >= 0
    # The current source image also returns the explicit bounded output without
    # creating the retired lowering capability.
    assert term.digits()
