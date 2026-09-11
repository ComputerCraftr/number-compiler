"""Complete finite proof of the decimal T² output-section factorization."""

from __future__ import annotations

import hashlib
import zlib
from dataclasses import FrozenInstanceError
from itertools import product
from pathlib import Path

import pytest

from number_compiler.arithmetic.contracts.block_kernel import _load_base10_t2_kernel
from number_compiler.hashlife.execution.diamond_reverse_kernel import (
    _FACTORIZATION_SHA256,
    certify_decimal_t2_factorization,
    factorization_payload,
    load_decimal_t2_factorization,
    validate_decimal_t2_factorization,
)


def test_certificate_exhausts_raw_surjection_and_every_output_pair() -> None:
    certified = certify_decimal_t2_factorization()
    loaded = load_decimal_t2_factorization()
    assert certified == loaded
    assert certified.verification.raw_left_states == 1423
    assert certified.verification.raw_right_states == 179
    assert certified.verification.transition_checks == (1423 + 179) * 20
    assert certified.verification.output_checks == 1423 * 179 * 20
    assert len(certified.left) == 757
    assert len(certified.right) == 179
    packed = zlib.compress(factorization_payload(certified), 9)
    assert hashlib.sha256(packed).hexdigest() == _FACTORIZATION_SHA256


def test_factorized_section_emits_exact_kernel_values_and_is_immutable() -> None:
    factor = load_decimal_t2_factorization()
    kernel = _load_base10_t2_kernel()
    for left, symbol, right in product((0, 1, 100, 756), range(20), (0, 1, 178)):
        assert factor.emit(left, symbol, right) == kernel.emit(left, symbol, right)
    assert load_decimal_t2_factorization() is factor
    with pytest.raises(FrozenInstanceError):
        setattr(factor, "left", ())
    with pytest.raises(FrozenInstanceError):
        setattr(factor.left[0], "anchor", 1)
    for arguments in ((-1, 0, 0), (757, 0, 0), (0, 20, 0), (0, 0, 179), (True, 0, 0)):
        with pytest.raises(ValueError):
            factor.emit(*arguments)


def test_factorization_loader_rejects_corrupt_artifact_before_decode(
    monkeypatch: pytest.MonkeyPatch,
) -> None:

    original = Path.read_bytes
    load_decimal_t2_factorization.cache_clear()

    def corrupt(path: Path) -> bytes:
        value = original(path)
        return (
            value + b"wrong" if path.name == "base10_t2_factorization.zlib" else value
        )

    with monkeypatch.context() as patch:
        patch.setattr(Path, "read_bytes", corrupt)
        with pytest.raises(ValueError, match="checksum"):
            load_decimal_t2_factorization()
    assert len(load_decimal_t2_factorization().left) == 757


def test_loader_binds_complete_current_base_kernel_tables(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.execution.diamond_reverse_kernel as module

    load_decimal_t2_factorization.cache_clear()
    original = module._base_tables()
    corrupted = (original[0], original[1], b"different", original[3])
    with monkeypatch.context() as patch:
        patch.setattr(module, "_base_tables", lambda: corrupted)
        with pytest.raises(ValueError, match="Base kernel"):
            load_decimal_t2_factorization()
    assert load_decimal_t2_factorization().base_outputs == original[2]


def test_fixed_content_validation_rejects_cached_object_mutation() -> None:
    factor = load_decimal_t2_factorization()
    original = factor.left
    try:
        object.__setattr__(factor, "left", (original[1], *original[1:]))
        assert load_decimal_t2_factorization() is factor
        assert not validate_decimal_t2_factorization(factor)
    finally:
        object.__setattr__(factor, "left", original)
    assert validate_decimal_t2_factorization(factor)
