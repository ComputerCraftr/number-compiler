"""Exact mixed Mahler source cylinders and radix-independent q-harmonic transport."""

from __future__ import annotations

import json
from typing import NoReturn

import pytest

import number_compiler.sequences.antihydra.mahler_mixed_harmonic_ring as mixed_ring_module
from number_compiler.arithmetic.fields.walsh import walsh64_mod5
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.mahler_border_identity import (
    MahlerOddMotifSignature,
)
from number_compiler.sequences.antihydra.mahler_mixed_harmonic_ring import (
    MahlerMixedOddHarmonicRing as Ring,
)
from number_compiler.sequences.antihydra.mahler_odd_macro import (
    MahlerOddToOddAction,
    odd_seam_packet,
    odd_seam_step,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm
from tests.support.mahler_harmonic_reference import (
    literal_q_harmonic_counts,
    source_for_motif,
)
from tests.support.mahler_harmonic_reference import (
    mapping as _mapping,
)


def _ring(source: int, word: tuple[int, ...]) -> Ring:
    return Ring.from_source(source, MahlerOddMotifSignature(word))


def _scalar_events(
    source: int, word: tuple[int, ...], copies: int, clock: int
) -> list[tuple[int, int, int, int, int, int]]:
    x = source
    q = (1 << clock) * (3 * x + 1)
    n = clock
    out = []
    for i in range(copies * len(word)):
        a = word[i % len(word)]
        assert ((3 * x + 1) & -(3 * x + 1)).bit_length() - 1 == a
        following = 3 ** (a - 1) * (3 * x + 1) // (1 << a)
        assert following & 1
        q_next = 3**a * q + (1 << (n + a))
        assert q_next == (1 << (n + a)) * (3 * following + 1)
        out.append((x, following, q, q_next, n, a))
        n += a
        x, q = following, q_next
    return out


@pytest.mark.parametrize("word", [(1, 2), (1, 1, 2), (2, 3), (1, 2, 1), (1, 3, 2)])
def test_mixed_word_powered_endpoint_and_every_crt_modulus(
    word: tuple[int, ...],
) -> None:
    x = source_for_motif(word, 7, extra_bits=6)
    ring = _ring(x, word)
    assert ring.capacity >= 7
    records = _scalar_events(x, word, 7, 11)
    for copies in range(8):
        expected = x if not copies else records[copies * len(word) - 1][1]
        assert ring.endpoint(copies) == expected
        assert ring.power(copies).advance(x, 0)[0] == expected
        for radix in (2, 3, 5, 6, 10, 64):
            for places in (1, 2, 3):
                assert (
                    ring.radix_residue(radix, places, copies)
                    == expected % radix**places
                )
    with pytest.raises(ValueError):
        _ring(x + (1 << ring.extent), word)
    with pytest.raises(ValueError):
        ring.power(ring.capacity + 1)


@pytest.mark.parametrize("word", [(1, 2), (1, 1, 2), (2, 3), (1, 2, 1)])
@pytest.mark.parametrize("radix", [2, 3, 5, 6, 10, 64])
def test_six_radix_q_carry_borrow_harmonics_match_literal_events(
    word: tuple[int, ...], radix: int
) -> None:
    copies = 22
    clock = 13
    x = source_for_motif(word, copies, extra_bits=6)
    ring = _ring(x, word)
    sp = ring.q_phase_spectrum(
        radix, 3, copies, clock=clock, walsh64=len(word) * copies >= 64
    )
    reference = _scalar_events(x, word, copies, clock)
    expected = literal_q_harmonic_counts(
        ((q, qnext, n, a) for _, _, q, qnext, n, a in reference),
        radix=radix,
        places=3,
    )
    assert sp.carry_phase_counts == expected[0]
    assert sp.borrow_phase_counts == expected[1]
    assert sp.xor_phase_counts == expected[2]
    if sp.period:
        future_classes = sp.future_moore_classes
        assert future_classes is not None
        assert 1 <= future_classes <= sp.prefix_length + sp.period
    else:
        # A finite observation that did not close its exact state orbit is
        # not evidence for any complete-future Moore class count.
        assert sp.future_moore_classes is None
    if sp.walsh64_xor is not None:
        assert len(sp.walsh64_xor) == 3
        for j in range(3):
            m = radix ** (j + 1)
            mask = 0
            for t, (_, _, q, qnext, n, a) in enumerate(reference[:64]):
                product = (3**a * (q % m)) % m
                addend = pow(2, n + a, m)
                carry = int(product + addend >= m)
                borrow = int((qnext % m) < (q % m))
                mask |= (carry ^ borrow) << t
            assert sp.walsh64_xor[j] == walsh64_mod5(mask)


def test_mixed_very_long_q_orbit_is_periodic_only_under_exact_source_guard() -> None:
    word = (1, 2)
    x = source_for_motif(word, 4096, extra_bits=6)
    ring = _ring(x, word)
    assert ring.capacity >= 4096
    q = ring.q_phase_spectrum(6, 2, 4096, clock=17, walsh64=True)
    assert q.prefix_length + q.period < 4096 * len(word)
    assert q.period > 0
    future_classes = q.future_moore_classes
    assert future_classes is not None
    assert 0 < future_classes <= q.prefix_length + q.period
    assert sum(sum(row) for row in q.xor_phase_counts) <= 4096 * 2 * 2
    walsh = q.walsh64_xor
    assert walsh is not None
    assert len(walsh) == 2


def test_bad_motif_and_unproved_repetition_fail_closed() -> None:
    x = source_for_motif((1, 2), 3, extra_bits=6)
    with pytest.raises(ValueError):
        _ring(x, (2, 1))
    with pytest.raises(ValueError):
        _ring(x, (1, 0))
    with pytest.raises(ValueError):
        _ring(x + 1, (1, 2))
    ring = _ring(x, (1, 2))
    with pytest.raises(ValueError):
        ring.q_phase_spectrum(5, 2, ring.capacity + 1, clock=0)
    with pytest.raises(ValueError):
        ring.q_phase_spectrum(5, 2, 2, clock=0, walsh64=True)


def test_structural_motif_identity_is_shared_but_source_guards_are_not() -> None:
    word = (1, 2)
    first = _ring(source_for_motif(word, 4), word)
    second = _ring(source_for_motif(word, 7), word)

    assert first.source != second.source
    assert first.macro_identity == second.macro_identity
    assert first.macro_identity.packet() == second.macro_identity.packet()
    assert first.capacity >= 4
    assert second.capacity >= 7
    assert first.endpoint(4) != second.endpoint(4)


def test_source_factory_does_not_recompile_its_authenticated_motif(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = source_for_motif((1, 2), 8, extra_bits=6)
    compile_motif = mixed_ring_module._compiled_motif
    calls = 0

    def counted(exponents: tuple[int, ...]) -> MahlerOddToOddAction:
        nonlocal calls
        calls += 1
        return compile_motif(exponents)

    monkeypatch.setattr(mixed_ring_module, "_compiled_motif", counted)
    _ring(source, (1, 2))
    assert calls == 1


def test_best_repeating_does_not_mask_arithmetic_invariant_failures(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def broken_discovery(*_args: object, **_kwargs: object) -> NoReturn:
        raise ArithmeticError("injected source-action invariant failure")

    monkeypatch.setattr(mixed_ring_module, "_discover_prefix_actions", broken_discovery)
    with pytest.raises(ArithmeticError, match="injected"):
        Ring.best_repeating(7)


def test_production_odd_seam_packet_includes_mixed_and_preserves_guard_split() -> None:
    p = odd_seam_packet(
        odd_seam_step(7, 0, 0, 0), bits=8, decimal_places=3, walsh=False
    )
    mixed = _mapping(p["source_bound_mixed_odd_ring"])
    motif = mixed["motif"]
    assert motif == (1, 1, 2)
    macro = _mapping(mixed["macro_identity"])
    assert macro["family"] == "antihydra"
    assert macro["kind"] == "path"
    assert macro["signature"] == ("mahler-odd-run-motif-v1", motif)
    assert mixed["repetitions"] == 2
    assert mixed["fractional_guard_empty"] is True
    assert mixed["ledger_minimum"] == 0
    q_harmonics = _mapping(mixed["q_temporal_harmonics"])
    assert set(q_harmonics) == {"2", "3", "5", "6", "10", "64"}
    endpoint_residues = _mapping(mixed["endpoint_radix_residues"])
    # The observer returns the exact three-place residue, not only the last
    # decimal digit; the literal two-motif endpoint is 201.
    assert endpoint_residues["10"] == 201
    json.dumps(p)
    old = odd_seam_packet(
        odd_seam_step(7, 0, 0, 0),
        bits=8,
        decimal_places=3,
        walsh=False,
        include_mixed_ring=False,
    )
    assert "source_bound_mixed_odd_ring" not in old
    for k in old:
        assert old[k] == p[k]


def test_authenticated_public_root_demand_is_lazy_and_nested_without_memo_replacement() -> (
    None
):
    term = AntihydraArithmeticTerm(0, shared_cache=False)
    result = term.result()
    ordinary = associated_action(result, include_radix_ports=False)
    assert "source_bound_odd_to_odd" not in ordinary
    demanded = associated_action(result, include_radix_ports=True)
    odd_packet = _mapping(demanded["source_bound_odd_to_odd"])
    mixed_packet = _mapping(odd_packet["source_bound_mixed_odd_ring"])
    fixed_packet = _mapping(odd_packet["source_bound_harmonic_ring"])
    assert mixed_packet["motif"] == (1, 1, 2)
    assert fixed_packet["powered_endpoint"] == 17
    demanded.pop("source_bound_odd_to_odd")
    # Every previous keyed public field remains identical across the demand;
    # the only legitimate extra old field is the deliberately requested radix
    # observation. The complete ordinary packet is still unchanged.
    for key, value in ordinary.items():
        assert demanded[key] == value
    assert term.mahler_workspace is not None
    assert term.mahler_workspace._window_memo is None
