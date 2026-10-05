"""Generate and independently check finite comma-child sector forests.

The certificate stores one record per reached decimal-sector entry. A record
contains the exact number of guarded phase cycles and *all* exits from the
remaining bounded boundary path. It never stores the skipped literal terms.
This is development evidence until its checker is refined in Isabelle.
"""

from __future__ import annotations

import argparse
import gzip
import io
import json
from collections import deque
from dataclasses import asdict, dataclass
from hashlib import sha256
from math import gcd
from pathlib import Path
from typing import BinaryIO

from devtools.experiments.comma.forest_certificate import (
    FIRST_FORK_CHILDREN,
    FIRST_FORK_VALUE,
    ROOTS,
    _boundary_children,
    _interior_cycles,
    _lead_and_scale,
    _literal_children,
    check_first_fork,
)
from number_compiler.resources.ledger import ResourceLedger

SCHEMA = "a367620-closed-sector-forest-v1"
RIGHT_FIRST_FORK_CHILD = 20_000_000_000
MAX_RECORD_BYTES = 8192


@dataclass(frozen=True, slots=True)
class CertificateMetrics:
    entries: int
    boundary_steps: int
    literal_candidates_checked: int
    maximum_boundary_run: int
    maximum_decimal_digits: int
    represented_cycles: int
    uncompressed_bytes: int
    compressed_bytes: int
    compressed_sha256: str


def _dump_line(stream: io.TextIOWrapper, value: dict[str, object]) -> int:
    line = json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n"
    stream.write(line)
    return len(line.encode("ascii"))


def _open_writer(raw: BinaryIO) -> io.TextIOWrapper:
    compressed = gzip.GzipFile(fileobj=raw, mode="wb", filename="", mtime=0)
    return io.TextIOWrapper(compressed, encoding="ascii", newline="\n")


def generate_closed_region(
    path: Path, *, include_excluded_roots: bool = True, include_right_child: bool = True
) -> CertificateMetrics:
    """Write canonical BFS records; source labels never merge across trees."""
    sources = [root for root in ROOTS if root != 20] if include_excluded_roots else []
    if include_right_child:
        sources.append(RIGHT_FIRST_FORK_CHILD)
    if not sources:
        raise ValueError("a closed-region certificate needs a source")
    frontier = deque((source, source) for source in sources)
    seen: set[tuple[int, int]] = set()
    entries = boundary_steps = max_run = max_digits = cycles = raw_bytes = 0
    prefix = check_first_fork(ResourceLedger(), 1_000_000)
    if (
        prefix.first_fork_value != FIRST_FORK_VALUE
        or prefix.children != FIRST_FORK_CHILDREN
    ):
        raise ValueError("first-fork source witness changed")
    with path.open("wb") as raw, _open_writer(raw) as writer:
        raw_bytes += _dump_line(
            writer,
            {
                "schema": SCHEMA,
                "sources": sources,
                "prefix": {
                    "index": prefix.first_fork_index,
                    "value": str(prefix.first_fork_value),
                    "children": [str(child) for child in prefix.children],
                },
            },
        )
        while frontier:
            source, entry = frontier.popleft()
            if (source, entry) in seen:
                raise ValueError("repeated sector entry in generated forest")
            seen.add((source, entry))
            entries += 1
            max_digits = max(max_digits, len(str(entry)))
            f, scale = _lead_and_scale(entry)
            boundary = (f + 1) * scale if f < 9 else 10 * scale
            k = entry
            full_cycles = 0
            if k >= 100:
                steps, gain = _interior_cycles(k, f, boundary)
                full_cycles = steps // (10 // gcd(f, 10))
                cycles += full_cycles
                k += gain
            exits: list[int] = []
            local_steps = 0
            while True:
                children = (
                    _literal_children(k) if k < 100 else _boundary_children(k, f, scale)
                )
                local_steps += 1
                boundary_steps += 1
                same: int | None = None
                for child in children:
                    if child < boundary and k >= 100:
                        if same is not None:
                            raise ValueError("multiple same-sector children")
                        same = child
                    else:
                        exits.append(child)
                        frontier.append((source, child))
                if same is None:
                    break
                k = same
            max_run = max(max_run, local_steps)
            raw_bytes += _dump_line(
                writer,
                {
                    "source": str(source),
                    "entry": str(entry),
                    "cycles": full_cycles,
                    "boundary_steps": local_steps,
                    "exits": [str(child) for child in exits],
                },
            )
    compressed_bytes = path.stat().st_size
    compressed_hash = sha256(path.read_bytes()).hexdigest()
    return CertificateMetrics(
        entries=entries,
        boundary_steps=boundary_steps,
        literal_candidates_checked=9 * boundary_steps,
        maximum_boundary_run=max_run,
        maximum_decimal_digits=max_digits,
        represented_cycles=cycles,
        uncompressed_bytes=raw_bytes,
        compressed_bytes=compressed_bytes,
        compressed_sha256=compressed_hash,
    )


def _no_duplicate_json_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate certificate key")
        result[key] = value
    return result


def _read_record(line: str) -> dict[str, object]:
    if len(line.encode("ascii")) > MAX_RECORD_BYTES:
        raise ValueError("certificate record exceeds 8192 bytes")
    value = json.loads(line, object_pairs_hook=_no_duplicate_json_keys)
    if not isinstance(value, dict):
        raise TypeError("certificate record must be an object")
    if json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n" != line:
        raise ValueError("certificate record is not canonical JSONL")
    return value


def _decimal(value: object) -> int:
    if not isinstance(value, str) or not value or value[0] == "0":
        raise ValueError("certificate integer is not canonical positive decimal")
    if not value.isascii() or not value.isdecimal():
        raise ValueError("certificate integer is not decimal")
    return int(value)


def _exact_children(k: int) -> tuple[int, ...]:
    """Independent nine-digit reference; no generator boundary helper used."""
    offset = 10 * (k % 10)
    children: list[int] = []
    for e in range(1, 10):
        child = k + offset + e
        if str(child)[0] == str(e):
            children.append(child)
    return tuple(children)


def _exact_period(f: int, d: int) -> tuple[int, int]:
    """Check a period using at most ten residue events, not a closed sum."""
    length = 10 // gcd(f, 10)
    residue = d
    displacement = 0
    for _ in range(length):
        displacement += 10 * residue + f
        residue = (residue + f) % 10
    if residue != d:
        raise ValueError("phase cycle does not close")
    return length, displacement


def _verify_prefix(raw_prefix: object) -> None:
    if not isinstance(raw_prefix, dict) or set(raw_prefix) != {
        "index",
        "value",
        "children",
    }:
        raise ValueError("missing first-fork prefix witness")
    index = raw_prefix["index"]
    if type(index) is not int or index <= 0:
        raise ValueError("invalid first-fork index")
    value = _decimal(raw_prefix["value"])
    children = raw_prefix["children"]
    if not isinstance(children, list):
        raise TypeError("invalid first-fork children")
    expected_children = tuple(_decimal(child) for child in children)
    k = 20
    actual_index = 1
    while True:
        digits = str(k)
        f = int(digits[0])
        scale = 10 ** (len(digits) - 1)
        boundary = (f + 1) * scale if f < 9 else 10 * scale
        if k >= 100:
            period, displacement = _exact_period(f, k % 10)
            full_cycles = max(0, (boundary - 100 - k) // displacement)
            k += full_cycles * displacement
            actual_index += full_cycles * period
        actual_children = _exact_children(k)
        if len(actual_children) != 1:
            if (actual_index, k, actual_children) != (
                index,
                value,
                expected_children,
            ):
                raise ValueError("first-fork prefix witness is false")
            return
        k = actual_children[0]
        actual_index += 1


def verify_closed_region(
    path: Path, *, max_entries: int = 131_072
) -> CertificateMetrics:
    """Stream every record and require exact closure of the BFS frontier.

    The sector arithmetic here is independent of the generator. Isabelle must
    still prove this bounded checker refines the full child relation before a
    checked instance can authorize public sequence terms.
    """
    compressed_bytes = path.stat().st_size
    compressed_hash = sha256(path.read_bytes()).hexdigest()
    entries = steps = max_run = max_digits = cycles = raw_bytes = 0
    with gzip.open(path, "rt", encoding="ascii", newline="\n") as stream:
        header = stream.readline(MAX_RECORD_BYTES + 1)
        raw_bytes += len(header.encode("ascii"))
        parsed_header = _read_record(header)
        if (
            set(parsed_header) != {"schema", "sources", "prefix"}
            or parsed_header["schema"] != SCHEMA
        ):
            raise ValueError("wrong certificate schema")
        _verify_prefix(parsed_header["prefix"])
        raw_sources = parsed_header["sources"]
        if not isinstance(raw_sources, list) or not raw_sources:
            raise ValueError("missing certificate sources")
        sources = [source for source in raw_sources if type(source) is int]
        if len(sources) != len(raw_sources) or any(source <= 0 for source in sources):
            raise ValueError("invalid certificate source")
        if len(set(sources)) != len(sources):
            raise ValueError("duplicate certificate source")
        frontier = deque((source, source) for source in sources)
        seen: set[tuple[int, int]] = set()
        while frontier:
            if entries >= max_entries:
                raise ValueError("certificate entry budget exhausted")
            line = stream.readline(MAX_RECORD_BYTES + 1)
            if not line:
                raise ValueError("truncated certificate frontier")
            raw_bytes += len(line.encode("ascii"))
            record = _read_record(line)
            if set(record) != {"source", "entry", "cycles", "boundary_steps", "exits"}:
                raise ValueError("incomplete certificate entry")
            source, entry = frontier.popleft()
            if (_decimal(record["source"]), _decimal(record["entry"])) != (
                source,
                entry,
            ):
                raise ValueError("certificate entry does not match frontier")
            if (source, entry) in seen:
                raise ValueError("cyclic or duplicated certificate entry")
            seen.add((source, entry))
            entries += 1
            max_digits = max(max_digits, len(str(entry)))
            full_cycles = record["cycles"]
            local_steps = record["boundary_steps"]
            if type(full_cycles) is not int or full_cycles < 0:
                raise ValueError("invalid cycle count")
            if type(local_steps) is not int or local_steps < 1:
                raise ValueError("invalid boundary-step count")
            f = int(str(entry)[0])
            scale = 10 ** (len(str(entry)) - 1)
            boundary = (f + 1) * scale if f < 9 else 10 * scale
            k = entry
            if k < 100:
                if full_cycles:
                    raise ValueError("small entry has a cycle skip")
            else:
                period, displacement = _exact_period(f, entry % 10)
                expected_cycles = max(0, (boundary - 100 - entry) // displacement)
                if full_cycles != expected_cycles:
                    raise ValueError("cycle count is not maximal guarded skip")
                k += full_cycles * displacement
                cycles += full_cycles
                if full_cycles and k > boundary - 100:
                    raise ValueError("cycle skip crossed boundary guard")
                if period > 10:
                    raise ValueError("phase period exceeds ten")
            exits: list[int] = []
            counted_steps = 0
            while True:
                children = _exact_children(k)
                counted_steps += 1
                steps += 1
                if counted_steps > 640:
                    raise ValueError("boundary walk exceeds fixed local bound")
                same: int | None = None
                for child in children:
                    if child < boundary and k >= 100:
                        if same is not None:
                            raise ValueError("multiple same-sector children")
                        same = child
                    else:
                        exits.append(child)
                if same is None:
                    break
                k = same
            if counted_steps != local_steps:
                raise ValueError("wrong boundary-step count")
            raw_exits = record["exits"]
            if not isinstance(raw_exits, list):
                raise TypeError("missing outgoing entries")
            parsed_exits = [_decimal(value) for value in raw_exits]
            if parsed_exits != exits:
                raise ValueError("incomplete or forged outgoing entries")
            frontier.extend((source, child) for child in exits)
            max_run = max(max_run, counted_steps)
        if stream.readline():
            raise ValueError("trailing certificate record")
    return CertificateMetrics(
        entries=entries,
        boundary_steps=steps,
        literal_candidates_checked=9 * steps,
        maximum_boundary_run=max_run,
        maximum_decimal_digits=max_digits,
        represented_cycles=cycles,
        uncompressed_bytes=raw_bytes,
        compressed_bytes=compressed_bytes,
        compressed_sha256=compressed_hash,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path, help="gzip JSONL certificate path")
    parser.add_argument("--verify", action="store_true", help="check an existing file")
    parser.add_argument(
        "--right-only",
        action="store_true",
        help="generate only the first fork's finite right branch",
    )
    args = parser.parse_args()
    if args.verify:
        metrics = verify_closed_region(args.path)
    else:
        metrics = generate_closed_region(
            args.path, include_excluded_roots=not args.right_only
        )
    print(json.dumps(asdict(metrics), sort_keys=True, indent=2))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
