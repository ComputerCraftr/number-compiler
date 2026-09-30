"""Independent finite-domain and archive adversaries for the C4² LEFT proof."""

from __future__ import annotations

import json
import zlib
from collections.abc import Mapping, Sequence
from dataclasses import replace
from pathlib import Path
from typing import TYPE_CHECKING, Never, cast

import pytest

from devtools.verification.block_composed import ComposedBlockEffect
from devtools.verification.block_runtime import _FunctionalBoundaryState
from devtools.verification.physical_c4_pair_certificate import (
    certificate_digest,
    generate_certificate,
    load_certificate,
    save_certificate,
    validate_certificate,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudget,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from number_compiler.arithmetic.contracts.physical_collatz_pair_certificate import (
    ARTIFACT_PATH,
    C4PairLeftCertificate,
    ReachableLeftState,
    load_verified_c4_pair_left,
)

if TYPE_CHECKING:
    import types


def signed(
    certificate: C4PairLeftCertificate,
) -> C4PairLeftCertificate:
    return replace(certificate, digest=certificate_digest(certificate))


def test_deterministic_artifact_and_complete_old_functional_carrier(
    tmp_path: Path,
) -> None:
    certificate = generate_certificate()
    assert certificate == load_verified_c4_pair_left() == load_certificate()
    assert (
        len(certificate.states),
        len(certificate.functions),
        certificate.encoded_bits,
    ) == (1234, 921, 11)
    path = tmp_path / "again.zlib"
    save_certificate(certificate, path)
    assert path.read_bytes() == ARTIFACT_PATH.read_bytes()
    primitive = PhysicalCollatzFourBlockEffect()
    context = ComposedBlockEffect(
        primitive,
        primitive,
        budget=BlockContextBudget(max_nodes=180000, max_cache_entries=180000),
    )
    states = context.boundary_universe(BoundarySide.LEFT, max_states=10000)
    assert states is not None and len(states) == len(certificate.states)
    for ordinal, (actual, encoded) in enumerate(
        zip(states, certificate.states, strict=True)
    ):
        assert isinstance(actual, _FunctionalBoundaryState)
        assert actual.anchor == encoded.anchor
        assert actual.image == certificate.functions[encoded.continuation]
        for symbol in range(3):
            assert (
                context.advance(BoundarySide.LEFT, actual, symbol)
                is states[certificate.transitions[ordinal][symbol]]
            )


@pytest.mark.parametrize(
    "field", ["anchor", "function", "transition", "predecessor", "initial", "kernel"]
)
def test_self_resigned_corruption_fails_equations_or_identity(field: str) -> None:
    original = load_verified_c4_pair_left()
    if field == "anchor":
        state = original.states[1]
        changed = replace(
            original,
            states=(
                original.states[0],
                replace(state, anchor=(state.anchor + 1) % 50),
                *original.states[2:],
            ),
        )
    elif field == "function":
        fn = original.functions[1]
        changed = replace(
            original,
            functions=(
                original.functions[0],
                ((fn[0] + 1) % 50, *fn[1:]),
                *original.functions[2:],
            ),
        )
    elif field == "transition":
        row = original.transitions[1]
        changed = replace(
            original,
            transitions=(
                original.transitions[0],
                ((row[0] + 1) % 1234, *row[1:]),
                *original.transitions[2:],
            ),
        )
    elif field == "predecessor":
        changed = replace(
            original,
            predecessors=(
                original.predecessors[0],
                (0, (original.predecessors[1][1] + 1) % 3),
                *original.predecessors[2:],
            ),
        )
    elif field == "initial":
        changed = replace(original, initial=1)
    else:
        changed = replace(original, kernel_digest="0" * 64)
    with pytest.raises(ValueError):
        validate_certificate(signed(changed))


@pytest.mark.parametrize("bad", [True, 0.0, -1, "0"])
def test_integer_aliases_reject_before_kernel_work(
    bad: bool | float | str, monkeypatch: pytest.MonkeyPatch
) -> None:
    original = load_verified_c4_pair_left()
    changed = replace(
        original, states=(ReachableLeftState(cast(int, bad), 0), *original.states[1:])
    )

    def poison(*args: object) -> Never:
        raise AssertionError("malformed certificate reached kernel work")

    monkeypatch.setattr(PhysicalCollatzFourBlockEffect, "validate", poison)
    with pytest.raises(ValueError):
        validate_certificate(signed(changed))


@pytest.mark.parametrize(
    "bad", [b"", b"not zlib", b"truncated", b"trailing", b"wrong types", b"oversized"]
)
def test_archive_rejects_malformed_trailing_or_oversized(
    tmp_path: Path, bad: bytes
) -> None:
    packed = ARTIFACT_PATH.read_bytes()
    if bad == b"truncated":
        packed = packed[:-1]
    elif bad == b"trailing":
        packed += b"x"
    elif bad == b"wrong types":
        raw = json.loads(zlib.decompress(packed))
        raw[5][0][0] = True
        packed = zlib.compress(json.dumps(raw).encode())
    elif bad == b"oversized":
        packed = zlib.compress(b" " * 8_000_001)
    else:
        packed = bad
    path = tmp_path / "bad.zlib"
    path.write_bytes(packed)
    with pytest.raises(ValueError):
        load_certificate(path)


def test_production_loader_never_trusts_self_signed_alternative(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    import number_compiler.arithmetic.contracts.physical_collatz_pair_certificate as domain

    load_verified_c4_pair_left()  # A previous successful call must not bypass verification.
    path = tmp_path / "modified.zlib"
    path.write_bytes(ARTIFACT_PATH.read_bytes() + b"x")
    monkeypatch.setattr(domain, "ARTIFACT_PATH", path)
    with pytest.raises(ValueError, match="checksum"):
        domain.load_verified_c4_pair_left()


def test_loader_does_not_import_proof_or_share_mutable_execution_cache(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import builtins

    original = builtins.__import__

    def guarded(
        name: str,
        globals: dict[str, object] | None = None,
        locals: Mapping[str, object] | None = None,
        fromlist: Sequence[str] = (),
        level: int = 0,
    ) -> types.ModuleType:
        if "proof" in name:
            raise AssertionError("production loader imported proof")
        return original(name, globals, locals, fromlist, level)

    monkeypatch.setattr(builtins, "__import__", guarded)
    first, second = load_verified_c4_pair_left(), load_verified_c4_pair_left()
    assert first == second and first is not second
    assert type(first) is C4PairLeftCertificate
    assert isinstance(ARTIFACT_PATH, Path)
