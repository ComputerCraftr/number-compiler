"""Shared guards for proving warm comma admissions avoid package I/O."""

from __future__ import annotations

import builtins
from collections.abc import Mapping, Sequence
from pathlib import Path

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.comma import certificates
from number_compiler.sequences.comma.future_authority import (
    SOURCE20_FIRST_FORK_CHILDREN,
    SOURCE20_FIRST_FORK_INDEX,
    SOURCE20_FIRST_FORK_VALUE,
)


def count_forest_certificate_verifications(
    monkeypatch: pytest.MonkeyPatch,
) -> list[tuple[Path, int]]:
    """Use the issuer result shape while retaining the real asset checksum path."""
    from number_compiler.sequences.comma import forest_verifier

    calls: list[tuple[Path, int]] = []

    def accept(
        path: Path, _ledger: ResourceLedger, max_work: int
    ) -> forest_verifier.ForestVerification:
        calls.append((path, max_work))
        return forest_verifier.ForestVerification(
            roots_exhausted=49,
            sector_entries=1,
            boundary_steps=0,
            phase_cycles=0,
            candidate_digit_trials=0,
            prefix_index=SOURCE20_FIRST_FORK_INDEX,
            prefix_value=SOURCE20_FIRST_FORK_VALUE,
            prefix_children=SOURCE20_FIRST_FORK_CHILDREN,
            compressed_bytes=0,
            uncompressed_bytes=0,
        )

    monkeypatch.setattr(forest_verifier, "verify_forest_certificate", accept)
    return calls


def forbid_certificate_asset_access(monkeypatch: pytest.MonkeyPatch) -> None:
    """Reject warm admission attempts to hash, load, or import the asset."""

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("cached admission attempted package I/O or hashing")

    original_import = builtins.__import__

    def no_forest_import(
        name: str,
        globals: Mapping[str, object] | None = None,
        locals: Mapping[str, object] | None = None,
        fromlist: Sequence[str] | None = None,
        level: int = 0,
    ) -> object:
        if name == "number_compiler.sequences.comma.forest_verifier":
            raise AssertionError("cached admission imported the forest verifier")
        return original_import(name, globals, locals, fromlist, level)

    monkeypatch.setattr(certificates, "files", forbidden)
    monkeypatch.setattr(certificates, "sha256", forbidden)
    monkeypatch.setattr(builtins, "__import__", no_forest_import)
