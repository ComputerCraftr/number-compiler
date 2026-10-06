"""Immutable verified reachable LEFT interface of physical C4;C4.

This is a distinct 1,234-state reachable interface, not the universal composed
state sort. The offline proof checks every transition on all original 90 ports.
Production loads only that fixed checksum-bound result, with no proof import,
source traversal, state discovery, or mutable shared execution cache.
"""

from __future__ import annotations

import json
import zlib
from dataclasses import dataclass
from hashlib import sha256
from importlib.resources import files
from pathlib import Path

from number_compiler.sequences.collatz.physical_kernel import (
    PhysicalCollatzFourBlockEffect,
)

_METADATA = (2, 2, 3, 50, 90, 0, 0, 4, 8, 7)
RAW_DIGEST = "03b8bcb979462baecd146755bd952f69880e26e14aad563fc370bb28f64963ba"
PACKED_DIGEST = "71b0e985f8f8ee9172cfb6b967cf7befe5d5d0b786e93d822e29ee6ee89d3fce"
ARTIFACT_PATH = (
    Path(str(files("number_compiler"))) / "kernels" / "physical_collatz_eight_left.zlib"
)


@dataclass(frozen=True, slots=True)
class ReachableLeftState:
    anchor: int
    continuation: int


@dataclass(frozen=True, slots=True)
class C4PairLeftCertificate:
    version: int
    kernel_digest: str
    initial: int
    functions: tuple[tuple[int, ...], ...]
    states: tuple[ReachableLeftState, ...]
    transitions: tuple[tuple[int, int, int], ...]
    predecessors: tuple[tuple[int, int], ...]
    digest: str

    @property
    def encoded_bits(self) -> int:
        return (len(self.states) - 1).bit_length()

    @property
    def profile_role(self) -> str:
        return "z-reachable-c4-left"

    @property
    def primitive_left_count(self) -> int:
        return _METADATA[3]

    @property
    def argument_count(self) -> int:
        return _METADATA[4]

    @property
    def anchor_width(self) -> int:
        return (self.primitive_left_count - 1).bit_length()


def kernel_digest(kernel: PhysicalCollatzFourBlockEffect) -> str:
    kernel.validate()
    return sha256(
        bytes(_METADATA)
        + kernel.left_transitions
        + kernel.right_transitions
        + kernel.outputs
    ).hexdigest()


def load_verified_c4_pair_left() -> C4PairLeftCertificate:
    """Verify fixed artifact/kernel bytes before exposing an immutable domain."""
    with ARTIFACT_PATH.open("rb") as stream:
        packed = stream.read(30_779)
    if len(packed) != 30_778 or sha256(packed).hexdigest() != PACKED_DIGEST:
        raise ValueError("reachable C4 pair artifact checksum mismatch")
    raw = zlib.decompress(packed)
    if sha256(raw).hexdigest() != RAW_DIGEST:
        raise ValueError("reachable C4 pair decompressed checksum mismatch")
    data = json.loads(raw)
    # Content hashes bind every field to the exhaustively checked artifact.
    # No caller-supplied record can self-attest by copying its digest field.
    if data[2] != list(_METADATA) or data[1] != kernel_digest(
        PhysicalCollatzFourBlockEffect()
    ):
        raise ValueError("reachable C4 pair kernel binding mismatch")
    return C4PairLeftCertificate(
        data[0],
        data[1],
        data[3],
        tuple(tuple(row) for row in data[4]),
        tuple(ReachableLeftState(*row) for row in data[5]),
        tuple(tuple(row) for row in data[6]),
        tuple(tuple(row) for row in data[7]),
        RAW_DIGEST,
    )
