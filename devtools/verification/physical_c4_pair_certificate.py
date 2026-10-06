"""Offline, source-free reachable LEFT certificate for the verified C4;C4.

Complete functions on the ORIGINAL 90-state opposite kernel domain are interned
separately. No composed Cartesian domain or source trajectory is enumerated.
This reachable interface does not redefine the universal arbitrary-state codec.
"""

from __future__ import annotations

import json
import zlib
from dataclasses import replace
from hashlib import sha256
from importlib.resources import files
from pathlib import Path

from devtools.verification import require_exact_oracle
from number_compiler.sequences.collatz.physical_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from number_compiler.sequences.collatz.physical_pair_certificate import (
    C4PairLeftCertificate,
    ReachableLeftState,
)
from number_compiler.sequences.collatz.physical_pair_certificate import (
    kernel_digest as _kernel_digest,
)

_VERSION = 1
_MAX_STATES = 10_000
_MAX_RAW = 8_000_000
_METADATA = (2, 2, 3, 50, 90, 0, 0, 4, 8, 7)
ARTIFACT_PATH = (
    Path(str(files("number_compiler"))) / "kernels" / "physical_collatz_eight_left.zlib"
)


def _payload(certificate: C4PairLeftCertificate) -> bytes:
    return json.dumps(
        [
            certificate.version,
            certificate.kernel_digest,
            list(_METADATA),
            certificate.initial,
            certificate.functions,
            [(state.anchor, state.continuation) for state in certificate.states],
            certificate.transitions,
            certificate.predecessors,
        ],
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("ascii")


def certificate_digest(certificate: C4PairLeftCertificate) -> str:
    """Content identity; callers must still validate shapes and equations."""
    return sha256(_payload(certificate)).hexdigest()


def _integer(value: object, stop: int) -> bool:
    return type(value) is int and 0 <= value < stop


def _shape(certificate: C4PairLeftCertificate) -> None:
    if type(certificate) is not C4PairLeftCertificate:
        raise ValueError("unrecognized certificate record")
    if type(certificate.version) is not int or certificate.version != _VERSION:
        raise ValueError("unsupported certificate version")
    for digest in (certificate.digest, certificate.kernel_digest):
        if (
            type(digest) is not str
            or len(digest) != 64
            or any(c not in "0123456789abcdef" for c in digest)
        ):
            raise ValueError("invalid certificate digest")
    collections = (
        certificate.functions,
        certificate.states,
        certificate.transitions,
        certificate.predecessors,
    )
    if any(
        type(values) is not tuple or not 0 < len(values) <= _MAX_STATES
        for values in collections
    ):
        raise ValueError("invalid certificate collection")
    count = len(certificate.states)
    if not _integer(certificate.initial, count) or certificate.initial != 0:
        raise ValueError("invalid initial ordinal")
    if len(certificate.transitions) != count or len(certificate.predecessors) != count:
        raise ValueError("incomplete certificate rows")
    for function in certificate.functions:
        if (
            type(function) is not tuple
            or len(function) != 90
            or any(not _integer(v, 50) for v in function)
        ):
            raise ValueError("invalid original-domain continuation")
    for state in certificate.states:
        if (
            type(state) is not ReachableLeftState
            or not _integer(state.anchor, 50)
            or not _integer(state.continuation, len(certificate.functions))
        ):
            raise ValueError("invalid reachable-state interpretation")
    for row in certificate.transitions:
        if (
            type(row) is not tuple
            or len(row) != 3
            or any(not _integer(v, count) for v in row)
        ):
            raise ValueError("invalid transition row")
    for index, predecessor in enumerate(certificate.predecessors):
        if (
            type(predecessor) is not tuple
            or len(predecessor) != 2
            or any(type(v) is not int for v in predecessor)
        ):
            raise ValueError("invalid predecessor witness")
        if index == 0:
            if predecessor != (-1, -1):
                raise ValueError("initial predecessor must be absent")
        elif not _integer(predecessor[0], index) or not _integer(predecessor[1], 3):
            raise ValueError("predecessor is not an earlier reachable state")


def validate_certificate(certificate: C4PairLeftCertificate) -> None:
    """Verify every transition on all 90 arguments, plus exact reachability.

    This deliberately runs offline inside an explicit proof context. Production
    may consume a separately checksum-bound immutable artifact, never this BFS.
    """
    require_exact_oracle()
    _shape(certificate)
    kernel = PhysicalCollatzFourBlockEffect()
    if certificate.kernel_digest != _kernel_digest(kernel):
        raise ValueError("certificate refers to a different kernel")
    if certificate.digest != certificate_digest(certificate):
        raise ValueError("certificate content digest mismatch")
    if len(set(certificate.functions)) != len(certificate.functions) or len(
        set(certificate.states)
    ) != len(certificate.states):
        raise ValueError("certificate contains noncanonical duplicate interpretations")
    initial = certificate.states[0]
    if initial.anchor != 0 or certificate.functions[initial.continuation] != (0,) * 90:
        raise ValueError("incorrect composed initial state")
    if {state.continuation for state in certificate.states} != set(
        range(len(certificate.functions))
    ):
        raise ValueError("unused continuation functions")
    for ordinal, state in enumerate(certificate.states):
        image = certificate.functions[state.continuation]
        for symbol, successor in enumerate(certificate.transitions[ordinal]):
            target = certificate.states[successor]
            target_image = certificate.functions[target.continuation]
            if target.anchor != kernel.left_transitions[3 * state.anchor + symbol]:
                raise ValueError("anchor transition equation fails")
            for argument in range(90):
                pulled = kernel.right_transitions[3 * argument + symbol]
                emitted = kernel.outputs[(state.anchor * 3 + symbol) * 90 + argument]
                if (
                    target_image[argument]
                    != kernel.left_transitions[3 * image[pulled] + emitted]
                ):
                    raise ValueError("continuation transition equation fails")
        if ordinal:
            predecessor, symbol = certificate.predecessors[ordinal]
            if certificate.transitions[predecessor][symbol] != ordinal:
                raise ValueError("reachability witness fails")


def generate_certificate() -> C4PairLeftCertificate:
    """Bounded deterministic BFS, independent of runtime state/provenance IDs."""
    require_exact_oracle()
    kernel = PhysicalCollatzFourBlockEffect()
    functions: list[tuple[int, ...]] = [(0,) * 90]
    function_ids = {functions[0]: 0}
    states = [ReachableLeftState(0, 0)]
    state_ids = {states[0]: 0}
    transitions: list[tuple[int, int, int]] = []
    predecessors = [(-1, -1)]
    cursor = 0
    while cursor < len(states):
        state = states[cursor]
        image = functions[state.continuation]
        successors = []
        for symbol in range(3):
            advanced = tuple(
                kernel.left_transitions[
                    3 * image[kernel.right_transitions[3 * q + symbol]]
                    + kernel.outputs[(state.anchor * 3 + symbol) * 90 + q]
                ]
                for q in range(90)
            )
            function = function_ids.get(advanced)
            if function is None:
                function = len(functions)
                function_ids[advanced] = function
                functions.append(advanced)
            target = ReachableLeftState(
                kernel.left_transitions[3 * state.anchor + symbol], function
            )
            successor = state_ids.get(target)
            if successor is None:
                if len(states) >= _MAX_STATES:
                    raise ValueError("reachable certificate state cap exceeded")
                successor = len(states)
                state_ids[target] = successor
                states.append(target)
                predecessors.append((cursor, symbol))
            successors.append(successor)
        transitions.append((successors[0], successors[1], successors[2]))
        cursor += 1
    certificate = C4PairLeftCertificate(
        _VERSION,
        _kernel_digest(kernel),
        0,
        tuple(functions),
        tuple(states),
        tuple(transitions),
        tuple(predecessors),
        "",
    )
    certificate = replace(certificate, digest=certificate_digest(certificate))
    validate_certificate(certificate)
    return certificate


def save_certificate(
    certificate: C4PairLeftCertificate, path: Path = ARTIFACT_PATH
) -> None:
    validate_certificate(certificate)
    path.write_bytes(zlib.compress(_payload(certificate), level=9))


def load_certificate(path: Path = ARTIFACT_PATH) -> C4PairLeftCertificate:
    require_exact_oracle()
    with path.open("rb") as stream:
        packed = stream.read(_MAX_RAW + 1)
    if len(packed) > _MAX_RAW:
        raise ValueError("oversized certificate archive")
    decoder = zlib.decompressobj()
    try:
        raw = decoder.decompress(packed, _MAX_RAW + 1)
        if (
            len(raw) > _MAX_RAW
            or not decoder.eof
            or decoder.unused_data
            or decoder.unconsumed_tail
        ):
            raise ValueError("oversized, truncated, or trailing certificate data")
        data = json.loads(raw)
        if type(data) is not list or len(data) != 8 or data[2] != list(_METADATA):
            raise ValueError("invalid certificate envelope")
        # Preserve numeric types: no int() coercions may hide bool/float aliases.
        certificate = C4PairLeftCertificate(
            data[0],
            data[1],
            data[3],
            tuple(tuple(row) for row in data[4]),
            tuple(ReachableLeftState(*row) for row in data[5]),
            tuple(tuple(row) for row in data[6]),
            tuple(tuple(row) for row in data[7]),
            sha256(raw).hexdigest(),
        )
        validate_certificate(certificate)
        if raw != _payload(certificate):
            raise ValueError("noncanonical certificate encoding")
        return certificate
    except (
        zlib.error,
        TypeError,
        IndexError,
        json.JSONDecodeError,
        UnicodeDecodeError,
    ) as exc:
        raise ValueError("malformed certificate archive") from exc
