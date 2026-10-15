"""Streaming checker for finite comma-child sector forests.

The checker deliberately shares no code with certificate generation.  It
reconstructs the root partition, the root-20 path, and every bounded sector
frontier using the literal child rule.  The certificate can abbreviate only
the checked arithmetic progressions inside a sector.
"""

from __future__ import annotations

import gzip
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Final

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import comma as _comma_keys
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.comma.arithmetic import phase_period
from number_compiler.sequences.comma.certificates import _charge

_SCHEMA: Final[str] = "a367620-closed-sector-forest-v1"
_MAX_LINE_BYTES = 8192
_MAX_COMPRESSED_BYTES = 8 * 1024 * 1024
_MAX_UNCOMPRESSED_BYTES = 64 * 1024 * 1024
_PREFIX_RIGHT_CHILD = 20_000_000_000


@dataclass(frozen=True, slots=True)
class ForestVerification:
    """Small counters returned after the complete stream has been checked."""

    roots_exhausted: int
    sector_entries: int
    boundary_steps: int
    phase_cycles: int
    candidate_digit_trials: int
    prefix_index: int
    prefix_value: int
    prefix_children: tuple[int, ...]
    compressed_bytes: int
    uncompressed_bytes: int

    def to_dict(self) -> dict[str, object]:
        return {
            "roots_exhausted": self.roots_exhausted,
            "sector_entries": self.sector_entries,
            "boundary_steps": self.boundary_steps,
            "phase_cycles": self.phase_cycles,
            "candidate_digit_trials": self.candidate_digit_trials,
            "prefix_index": self.prefix_index,
            "prefix_value": self.prefix_value,
            "prefix_children": list(self.prefix_children),
            "compressed_bytes": self.compressed_bytes,
            "uncompressed_bytes": self.uncompressed_bytes,
        }


def _charge_bits(ledger: ResourceLedger, *values: int) -> None:
    ledger.bump(
        _comma_keys.COMMA_CERTIFICATE_OPERAND_BIT_WORK,
        sum(v.bit_length() for v in values),
    )


def _leading_digit_scale(value: int) -> tuple[int, int]:
    if type(value) is not int or value <= 0:
        raise ValueError("comma forest values must be positive integers")
    # Estimate the decimal exponent from the bit length, then correct using
    # exact integer comparisons.  This avoids repeated huge-int-to-string
    # conversions while classifying the nine possible children.
    exponent = ((value.bit_length() - 1) * 30_103) // 100_000
    scale = 10**exponent
    while scale > value:
        scale //= 10
    while scale * 10 <= value:
        scale *= 10
    return value // scale, scale


def _child(parent: int, leading_digit: int) -> int:
    return parent + 10 * (parent % 10) + leading_digit


def _is_child(parent: int, candidate: int) -> bool:
    if candidate <= parent:
        return False
    lead, _ = _leading_digit_scale(candidate)
    return candidate == _child(parent, lead)


def _literal_children(parent: int) -> tuple[int, ...]:
    out: list[int] = []
    for digit in range(1, 10):
        candidate = _child(parent, digit)
        if _leading_digit_scale(candidate)[0] == digit:
            out.append(candidate)
    return tuple(out)


def _small_roots(ledger: ResourceLedger, max_work: int) -> tuple[int, ...]:
    roots: list[int] = []
    for value in range(1, 100):
        _charge(ledger, max_work)
        lead, _ = _leading_digit_scale(value)
        defect = (value - lead) % 10
        predecessor = value - 10 * defect - lead
        if predecessor <= 0:
            roots.append(value)
        elif not _is_child(predecessor, value):
            raise ValueError("independent comma predecessor classification failed")
        _charge_bits(ledger, value, predecessor)
    if len(roots) != 50 or 20 not in roots:
        raise ValueError("comma root partition is not the expected exact partition")
    return tuple(roots)


def _sector_upper(leading: int, scale: int) -> int:
    return (leading + 1) * scale if leading < 9 else 10 * scale


def _max_safe_cycles(value: int, leading: int, upper: int) -> tuple[int, int, int]:
    period, displacement = _phase_period(leading, value % 10)
    cycles = max(0, (upper - 100 - value) // displacement)
    return cycles, period, displacement


def _prefix_to_first_fork(
    ledger: ResourceLedger, max_work: int
) -> tuple[int, int, tuple[int, ...], int]:
    value = 20
    index = 1
    skipped_periods = 0
    while True:
        _charge(ledger, max_work)
        lead, scale = _leading_digit_scale(value)
        upper = _sector_upper(lead, scale)
        if value >= 100:
            cycles, period, displacement = _max_safe_cycles(value, lead, upper)
            if cycles:
                gain = cycles * displacement
                if value + gain > upper - 100:
                    raise ValueError("comma prefix skip crosses its guarded sector")
                value += gain
                index += cycles * period
                skipped_periods += cycles
                _charge(ledger, max_work)
                _charge_bits(ledger, value, gain, cycles, period)
        _charge(ledger, max_work)
        ledger.bump(
            _comma_keys.COMMA_CERTIFICATE_CANDIDATE_OPERAND_BIT_WORK,
            18 * value.bit_length(),
        )
        children = _literal_children(value)
        ledger.bump(_comma_keys.COMMA_CERTIFICATE_CANDIDATE_DIGIT_TRIALS, 9)
        ledger.bump(_comma_keys.COMMA_CERTIFICATE_BOUNDARY_CLASSIFICATIONS)
        if len(children) != 1:
            return index, value, children, skipped_periods
        value = children[0]
        index += 1


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key in comma certificate")
        result[key] = value
    return result


def _parse_line(line: bytes) -> dict[str, Any]:
    if len(line) > _MAX_LINE_BYTES or not line.endswith(b"\n"):
        raise ValueError("truncated or oversized comma certificate record")
    try:
        decoded = line.decode("ascii")
        obj = json.loads(decoded, object_pairs_hook=_strict_object)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError("malformed comma certificate JSON") from error
    if type(obj) is not dict:
        raise ValueError("comma certificate records must be JSON objects")
    canonical = (
        json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n"
    ).encode("ascii")
    if canonical != line:
        raise ValueError("comma certificate JSON is not canonical")
    return obj


def _positive_decimal(value: object, field: str) -> int:
    if type(value) is not str or not value or not value.isascii():
        raise ValueError(f"comma certificate {field} must be a decimal string")
    if value[0] == "0" or not value.isdecimal():
        raise ValueError(f"comma certificate {field} is not canonical positive decimal")
    parsed = int(value)
    if parsed <= 0:
        raise ValueError(f"comma certificate {field} is not canonical positive decimal")
    return parsed


def _check_header(
    header: dict[str, Any],
    roots: tuple[int, ...],
    prefix: tuple[int, int, tuple[int, ...], int],
) -> tuple[int, ...]:
    if (
        set(header) != {"schema", "sources", "prefix"}
        or header.get("schema") != _SCHEMA
    ):
        raise ValueError("unsupported comma forest certificate header")
    sources = header.get("sources")
    expected_sources = tuple(root for root in roots if root != 20) + (
        _PREFIX_RIGHT_CHILD,
    )
    if (
        type(sources) is not list
        or any(type(source) is not int for source in sources)
        or tuple(sources) != expected_sources
    ):
        raise ValueError(
            "comma certificate source partition differs from recomputation"
        )
    supplied_prefix = header.get("prefix")
    if type(supplied_prefix) is not dict or set(supplied_prefix) != {
        "index",
        "value",
        "children",
    }:
        raise ValueError("malformed comma first-fork prefix header")
    index, value, children, _ = prefix
    if (
        type(supplied_prefix["index"]) is not int
        or supplied_prefix["index"] != index
        or supplied_prefix["value"] != str(value)
        or type(supplied_prefix["children"]) is not list
        or supplied_prefix["children"] != [str(child) for child in children]
    ):
        raise ValueError(
            "comma first-fork prefix differs from independent recomputation"
        )
    return expected_sources


def _append_frontier(
    ledger: ResourceLedger,
    owner: int,
    frontier: LedgerList[tuple[int, int]],
    source: int,
    entry: int,
) -> None:
    ledger.reserve(owner, entries=1, nodes=1)
    try:
        frontier.append((source, entry))
    except BaseException:
        ledger.release(owner, entries=1, nodes=1)
        raise


def _verified_record(record: dict[str, Any], source: int, entry: int) -> None:
    if set(record) != {"source", "entry", "cycles", "boundary_steps", "exits"}:
        raise ValueError("malformed comma forest row")
    if _positive_decimal(record.get("source"), "source") != source:
        raise ValueError("comma forest row has the wrong source")
    if _positive_decimal(record.get("entry"), "entry") != entry:
        raise ValueError("comma forest row is missing or out of BFS order")


def _check_forest_row(
    record: dict[str, Any],
    source: int,
    entry: int,
    ledger: ResourceLedger,
    max_work: int,
) -> tuple[int, ...]:
    _verified_record(record, source, entry)
    _charge(ledger, max_work)
    lead, scale = _leading_digit_scale(entry)
    upper = _sector_upper(lead, scale)
    cycles = 0
    if entry >= 100:
        cycles, period, displacement = _max_safe_cycles(entry, lead, upper)
        gain = cycles * displacement
        if cycles and entry + gain > upper - 100:
            raise ValueError("certificate cycle skip crosses its guarded sector")
        value = entry + gain
        _charge_bits(ledger, entry, upper, cycles, displacement, gain, period)
    else:
        value = entry

    if entry < 100:
        _charge(ledger, max_work)
        ledger.bump(
            _comma_keys.COMMA_CERTIFICATE_CANDIDATE_OPERAND_BIT_WORK,
            18 * entry.bit_length(),
        )
        exits = list(_literal_children(entry))
        ledger.bump(_comma_keys.COMMA_CERTIFICATE_CANDIDATE_DIGIT_TRIALS, 9)
        ledger.bump(_comma_keys.COMMA_CERTIFICATE_BOUNDARY_CLASSIFICATIONS)
        boundary_steps = 1
        ledger.bump(_comma_keys.COMMA_CERTIFICATE_BOUNDARY_STEPS)
        for child in exits:
            _charge_bits(ledger, entry, child)
            if not _is_child(entry, child):
                raise ValueError("small comma child has an inconsistent parent")
    else:
        boundary_steps = 0
        exits = []
        while True:
            _charge(ledger, max_work)
            ledger.bump(
                _comma_keys.COMMA_CERTIFICATE_CANDIDATE_OPERAND_BIT_WORK,
                18 * value.bit_length(),
            )
            children = _literal_children(value)
            ledger.bump(_comma_keys.COMMA_CERTIFICATE_CANDIDATE_DIGIT_TRIALS, 9)
            ledger.bump(_comma_keys.COMMA_CERTIFICATE_BOUNDARY_CLASSIFICATIONS)
            boundary_steps += 1
            ledger.bump(_comma_keys.COMMA_CERTIFICATE_BOUNDARY_STEPS)
            same_sector: int | None = None
            for child in children:
                _charge_bits(ledger, value, child)
                if not _is_child(value, child):
                    raise ValueError("literal comma child has an inconsistent parent")
                if child < upper:
                    if same_sector is not None:
                        raise ValueError(
                            "comma transition has multiple same-sector children"
                        )
                    same_sector = child
                else:
                    exits.append(child)
            if same_sector is None:
                break
            value = same_sector

    row_cycles = record.get("cycles")
    row_steps = record.get("boundary_steps")
    row_exits = record.get("exits")
    parsed_exits = (
        tuple(_positive_decimal(child, "exit") for child in row_exits)
        if type(row_exits) is list
        else ()
    )
    if (
        type(row_cycles) is not int
        or row_cycles != cycles
        or type(row_steps) is not int
        or row_steps != boundary_steps
        or type(row_exits) is not list
        or parsed_exits != tuple(exits)
    ):
        raise ValueError("comma forest row disagrees with guarded literal expansion")
    return tuple(exits)


def verify_forest_certificate(
    path: str | Path,
    ledger: ResourceLedger,
    max_work: int,
    *,
    expected_sha256: str | None = None,
) -> ForestVerification:
    """Validate one complete finite forest and source-20 fork witness.

    Certificate bytes are streamed.  Only one bounded line and two ledger-
    owned BFS layers are retained at once.
    """
    if not isinstance(ledger, ResourceLedger):
        raise TypeError("ledger must be a ResourceLedger")
    if type(max_work) is not int or max_work < 1:
        raise ValueError("max_work must be a positive integer")
    if expected_sha256 is not None and (
        type(expected_sha256) is not str
        or len(expected_sha256) != 64
        or any(c not in "0123456789abcdef" for c in expected_sha256)
    ):
        raise ValueError("expected_sha256 must be a lowercase SHA-256 digest")
    certificate_path = Path(path)
    if not certificate_path.is_file():
        raise ValueError("comma forest certificate does not exist")

    candidate_trials_before = ledger.counters.get(
        _comma_keys.COMMA_CERTIFICATE_CANDIDATE_DIGIT_TRIALS, 0
    )
    if expected_sha256 is not None:
        digest = hashlib.sha256()
        compressed_bytes = 0
        with certificate_path.open("rb") as compressed:
            while True:
                _charge(ledger, max_work)
                chunk = compressed.read(16 * 1024)
                if not chunk:
                    break
                compressed_bytes += len(chunk)
                if compressed_bytes > _MAX_COMPRESSED_BYTES:
                    raise ValueError(
                        "comma certificate exceeds its compressed size limit"
                    )
                ledger.bump(_comma_keys.COMMA_CERTIFICATE_READ_BYTES, len(chunk))
                ledger.bump(
                    _comma_keys.COMMA_CERTIFICATE_OPERAND_BIT_WORK, 8 * len(chunk)
                )
                digest.update(chunk)
        if digest.hexdigest() != expected_sha256:
            raise ValueError("comma certificate checksum differs from expected digest")
    else:
        compressed_bytes = certificate_path.stat().st_size
        if compressed_bytes > _MAX_COMPRESSED_BYTES:
            raise ValueError("comma certificate exceeds its compressed size limit")

    owner_suffix = ledger.owner_count
    owner_a = ledger.register(
        f"comma-certificate-frontier-a-{owner_suffix}", "certificate_frontier"
    )
    owner_b = ledger.register(
        f"comma-certificate-frontier-b-{owner_suffix}", "certificate_frontier"
    )
    current: LedgerList[tuple[int, int]] = ledger.make_list(owner_a, append_only=False)
    following: LedgerList[tuple[int, int]] = ledger.make_list(
        owner_b, append_only=False
    )
    current_owner, following_owner = owner_a, owner_b
    uncompressed_bytes = sector_entries = boundary_steps = phase_cycles = 0
    prefix_index = prefix_value = 0
    prefix_children: tuple[int, ...] = ()
    reserved_a = reserved_b = 0
    frontier_peak = 0

    def append(
        owner: int, target: LedgerList[tuple[int, int]], root: int, item: int
    ) -> None:
        nonlocal reserved_a, reserved_b, frontier_peak
        _append_frontier(ledger, owner, target, root, item)
        if owner == owner_a:
            reserved_a += 1
        else:
            reserved_b += 1
        frontier_peak = max(frontier_peak, len(current) + len(following))

    try:
        roots = _small_roots(ledger, max_work)
        prefix = _prefix_to_first_fork(ledger, max_work)
        prefix_index, prefix_value, prefix_children, skipped = prefix
        if prefix_children != (19_999_999_999, _PREFIX_RIGHT_CHILD):
            raise ValueError(
                "root-20 first fork differs from the checked branch witness"
            )
        ledger.bump(_comma_keys.COMMA_CERTIFICATE_PREFIX_PHASE_CYCLES, skipped)

        with gzip.open(certificate_path, "rb") as stream:
            header_line = stream.readline(_MAX_LINE_BYTES + 1)
            uncompressed_bytes += len(header_line)
            if uncompressed_bytes > _MAX_UNCOMPRESSED_BYTES:
                raise ValueError(
                    "comma certificate exceeds its uncompressed size limit"
                )
            ledger.bump(
                _comma_keys.COMMA_CERTIFICATE_UNCOMPRESSED_BYTES, len(header_line)
            )
            header = _parse_line(header_line)
            sources = _check_header(header, roots, prefix)
            for source in sources:
                append(current_owner, current, source, source)

            while current:
                cursor = 0
                while cursor < len(current):
                    source, entry = current[cursor]
                    cursor += 1
                    line = stream.readline(_MAX_LINE_BYTES + 1)
                    uncompressed_bytes += len(line)
                    if len(line) > _MAX_LINE_BYTES or not line.endswith(b"\n"):
                        raise ValueError("truncated or oversized comma certificate row")
                    if uncompressed_bytes > _MAX_UNCOMPRESSED_BYTES:
                        raise ValueError(
                            "comma certificate exceeds its uncompressed size limit"
                        )
                    ledger.bump(
                        _comma_keys.COMMA_CERTIFICATE_UNCOMPRESSED_BYTES, len(line)
                    )
                    _charge(ledger, max_work)
                    record = _parse_line(line)
                    exits = _check_forest_row(record, source, entry, ledger, max_work)
                    sector_entries += 1
                    boundary_steps += int(record["boundary_steps"])
                    phase_cycles += int(record["cycles"])
                    for child in exits:
                        append(following_owner, following, source, child)

                # Drop the consumed BFS layer before promoting its successor.
                consumed = len(current)
                current.clear()
                ledger.release(current_owner, entries=consumed, nodes=consumed)
                if current_owner == owner_a:
                    reserved_a = 0
                else:
                    reserved_b = 0
                current, following = following, current
                current_owner, following_owner = following_owner, current_owner

            # A complete finite forest must have consumed exactly every row.
            trailing = stream.readline(_MAX_LINE_BYTES + 1)
            if trailing:
                raise ValueError("comma forest certificate contains extraneous rows")
            # Reading through EOF validates gzip CRC/trailer even when the last
            # data line happened to end exactly at a decompressor boundary.
            while stream.read(16 * 1024):
                raise ValueError("comma forest certificate contains trailing data")

        if sector_entries == 0:
            raise ValueError("comma forest certificate has no finite-forest rows")
        ledger.bump(_comma_keys.COMMA_CERTIFICATE_SECTOR_ENTRIES, sector_entries)
        ledger.bump(_comma_keys.COMMA_CERTIFICATE_PHASE_CYCLES, phase_cycles)
        ledger.counters[_comma_keys.COMMA_CERTIFICATE_FRONTIER_PEAK] = max(
            ledger.counters.get(_comma_keys.COMMA_CERTIFICATE_FRONTIER_PEAK, 0),
            frontier_peak,
        )
        return ForestVerification(
            roots_exhausted=49,
            sector_entries=sector_entries,
            boundary_steps=boundary_steps,
            phase_cycles=phase_cycles,
            candidate_digit_trials=(
                ledger.counters.get(
                    _comma_keys.COMMA_CERTIFICATE_CANDIDATE_DIGIT_TRIALS, 0
                )
                - candidate_trials_before
            ),
            prefix_index=prefix_index,
            prefix_value=prefix_value,
            prefix_children=prefix_children,
            compressed_bytes=compressed_bytes,
            uncompressed_bytes=uncompressed_bytes,
        )
    except (OSError, EOFError, gzip.BadGzipFile) as error:
        raise ValueError(
            "comma forest certificate is not a valid complete gzip stream"
        ) from error
    finally:
        for owner, store, reserved in (
            (owner_a, current if current_owner == owner_a else following, reserved_a),
            (owner_b, current if current_owner == owner_b else following, reserved_b),
        ):
            if len(store):
                store.clear()
            if reserved:
                ledger.release(owner, entries=reserved, nodes=reserved)
            ledger.mark_disposed(owner)


def _phase_period(leading: int, last_digit: int) -> tuple[int, int]:
    return phase_period(leading, last_digit)
