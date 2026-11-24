"""Reconcile bounded, run-scoped Isabelle proof-stage event records.

Records are diagnostic only and never grant proof authority or extend a guard.
Each complete UTF-8 JSON line carries its producing run and session. Events
from a reused heap, another run, or an inactive prerequisite are rejected.
"""

from __future__ import annotations

import json
import os
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Literal, TypedDict, TypeGuard
from uuid import uuid4

from number_compiler.arithmetic.contracts.input_validation import is_object_dictionary

_MAX_LINE = 16 * 1024
_MAX_ACTIVE = 4096
_MAX_INVOCATIONS = 100_000
_FIELDS = frozenset(
    {
        "run",
        "session",
        "lane",
        "invocation",
        "parent",
        "stage",
        "root",
        "event",
        "sequence",
    }
)
EventKind = Literal["start", "done", "fail"]


class EventRecord(TypedDict):
    run: str
    session: str
    lane: str
    invocation: str
    parent: str | None
    stage: str
    root: int | None
    event: EventKind
    sequence: int


class ActiveRecord(EventRecord):
    elapsed_observed_seconds: float


class ProgressReport(TypedDict):
    run: str
    session: str
    scope: Literal["requested", "prerequisite"]
    active: list[ActiveRecord]
    last_completed_by_lane: dict[str, EventRecord]
    elapsed_clock: Literal["guard-monotonic-observation"]
    pending_records: int
    last_completed: EventRecord | None
    last_failure: EventRecord | None
    rejected: int
    partial_line_bytes: int


class ProgressFileReport(ProgressReport):
    sidecar_path: str
    read_error: str | None
    consumed_bytes: int
    unread_bytes: int | None


@dataclass(frozen=True, slots=True)
class ProofEvent:
    run: str
    session: str
    lane: str
    invocation: str
    parent: str | None
    stage: str
    root: int | None
    event: EventKind
    sequence: int


def _record(event: ProofEvent) -> EventRecord:
    return {
        "run": event.run,
        "session": event.session,
        "lane": event.lane,
        "invocation": event.invocation,
        "parent": event.parent,
        "stage": event.stage,
        "root": event.root,
        "event": event.event,
        "sequence": event.sequence,
    }


def proof_progress_mode(environment: Mapping[str, str]) -> str:
    """Select coarse checkpoints independently of detailed proof profiling."""
    return environment.get("NUMBER_COMPILER_PROOF_PROGRESS", "coarse")


def _event_text(value: object) -> str | None:
    return value if type(value) is str and value and len(value) <= 256 else None


def _is_event_kind(value: object) -> TypeGuard[EventKind]:
    return type(value) is str and value in ("start", "done", "fail")


def _event(line: bytes) -> ProofEvent | None:
    try:

        def unique_pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
            result: dict[str, object] = {}
            for key, item in pairs:
                if key in result:
                    raise ValueError("duplicate proof event field")
                result[key] = item
            return result

        value: object = json.loads(line.decode("utf-8"), object_pairs_hook=unique_pairs)
    except (UnicodeDecodeError, ValueError, RecursionError):
        return None
    if not is_object_dictionary(value) or frozenset(value) != _FIELDS:
        return None
    run, session, lane, invocation, stage = (
        _event_text(value[key])
        for key in ("run", "session", "lane", "invocation", "stage")
    )
    if (
        run is None
        or session is None
        or lane is None
        or invocation is None
        or stage is None
    ):
        return None
    parent = value["parent"]
    if parent is not None and (
        type(parent) is not str or not parent or len(parent) > 256
    ):
        return None
    root = value["root"]
    if root is not None and (type(root) is not int or root < 0):
        return None
    sequence = value["sequence"]
    if type(sequence) is not int or sequence < 0:
        return None
    event = value["event"]
    if not _is_event_kind(event):
        return None
    return ProofEvent(
        run, session, lane, invocation, parent, stage, root, event, sequence
    )


class ProofProgress:
    """Track active nested invocations in each session/lane for one guard run."""

    def __init__(
        self,
        run_id: str,
        requested_sessions: frozenset[str],
        admitted_sessions: frozenset[str] | None = None,
    ) -> None:
        if type(run_id) is not str or not run_id or len(run_id) > 256:
            raise ValueError("invalid proof run identifier")
        if type(requested_sessions) is not frozenset or any(
            type(session) is not str or not session for session in requested_sessions
        ):
            raise ValueError("invalid requested session set")
        self.run_id = run_id
        self.requested_sessions = requested_sessions
        self.admitted_sessions = (
            admitted_sessions if admitted_sessions is not None else requested_sessions
        )
        if not requested_sessions <= self.admitted_sessions:
            raise ValueError("requested sessions are not admitted")
        self._pending: list[tuple[ProofEvent, float]] = []
        self._observation_time = 0.0
        self._starts: dict[tuple[str, str, str], float] = {}
        self._lane_completed: dict[tuple[str, str], ProofEvent] = {}
        self._partial = bytearray()
        self._discard = False
        self._last_sequence: dict[str, int] = {}
        self._active: dict[tuple[str, str, str], ProofEvent] = {}
        self._seen: set[tuple[str, str, str]] = set()
        self._completed: dict[str, ProofEvent] = {}
        self._failures: dict[str, ProofEvent] = {}
        self.rejected = 0

    def observe(
        self,
        data: bytes,
        active_sessions: frozenset[str],
        now: float = 0.0,
        retired_sessions: frozenset[str] = frozenset(),
    ) -> None:
        """Consume complete records only; an unfinished final record is ignored."""
        self._observation_time = max(self._observation_time, now)
        pending, self._pending = self._pending, []
        for event, observed_at in pending:
            if event.session in active_sessions:
                self._apply(event, observed_at)
            else:
                self._pending.append((event, observed_at))
        for byte in data:
            if self._discard:
                if byte == 10:
                    self._discard = False
                continue
            if byte == 10:
                self._consume(bytes(self._partial), active_sessions, retired_sessions)
                self._partial.clear()
            else:
                self._partial.append(byte)
                if len(self._partial) > _MAX_LINE:
                    self._partial.clear()
                    self._discard = True
                    self.rejected += 1

    def _consume(
        self,
        line: bytes,
        active_sessions: frozenset[str],
        retired_sessions: frozenset[str],
    ) -> None:
        event = _event(line)
        if (
            event is None
            or event.run != self.run_id
            or event.session not in self.admitted_sessions
            or event.sequence <= self._last_sequence.get(event.session, -1)
        ):
            self.rejected += 1
            return
        self._last_sequence[event.session] = event.sequence
        key = (event.session, event.lane, event.invocation)
        if event.session in retired_sessions and (
            event.event == "start" or key not in self._active
        ):
            self.rejected += 1
            return
        if event.session not in active_sessions:
            if len(self._pending) >= _MAX_ACTIVE:
                self.rejected += 1
            else:
                self._pending.append((event, self._observation_time))
            return
        self._apply(event, self._observation_time)

    def _apply(self, event: ProofEvent, observed_at: float) -> None:
        key = (event.session, event.lane, event.invocation)
        if event.event == "start":
            parent_key = (event.session, event.lane, event.parent)
            if (
                key in self._seen
                or len(self._seen) >= _MAX_INVOCATIONS
                or (len(self._active) >= _MAX_ACTIVE)
                or (event.parent is not None and parent_key not in self._active)
            ):
                self.rejected += 1
                return
            self._active[key] = event
            self._starts[key] = observed_at
            self._seen.add(key)
        else:
            started = self._active.get(key)
            if (
                started is None
                or (started.stage, started.root, started.parent)
                != (event.stage, event.root, event.parent)
                or any(
                    child.session == event.session
                    and child.lane == event.lane
                    and child.parent == event.invocation
                    for child in self._active.values()
                )
            ):
                self.rejected += 1
                return
            del self._active[key]
            del self._starts[key]
            if event.event == "done":
                self._lane_completed[(event.session, event.lane)] = event
            (self._completed if event.event == "done" else self._failures)[
                event.session
            ] = event

    def report(self, session: str) -> ProgressReport:
        """Describe the named session, separating target from prerequisite work."""
        active = [
            (key, event)
            for key, event in self._active.items()
            if event.session == session
            and not any(
                child.session == session
                and child.lane == event.lane
                and child.parent == event.invocation
                for child in self._active.values()
            )
        ]
        return {
            "run": self.run_id,
            "session": session,
            "scope": "requested"
            if session in self.requested_sessions
            else "prerequisite",
            "active": [
                {
                    **_record(event),
                    "elapsed_observed_seconds": max(
                        0.0, self._observation_time - self._starts[key]
                    ),
                }
                for key, event in active
            ],
            "last_completed_by_lane": {
                lane: _record(event)
                for (owner, lane), event in self._lane_completed.items()
                if owner == session
            },
            "elapsed_clock": "guard-monotonic-observation",
            "pending_records": sum(
                1 for event, _ in self._pending if event.session == session
            ),
            "last_completed": _record(self._completed[session])
            if session in self._completed
            else None,
            "last_failure": _record(self._failures[session])
            if session in self._failures
            else None,
            "rejected": self.rejected,
            "partial_line_bytes": len(self._partial),
        }


class ProofProgressFile:
    """Read a fresh sidecar incrementally with bounded work per poll."""

    def __init__(
        self,
        path: Path,
        run_id: str,
        requested_sessions: frozenset[str],
        admitted_sessions: frozenset[str] | None = None,
    ) -> None:
        self.path = path
        self.progress = ProofProgress(run_id, requested_sessions, admitted_sessions)
        self.offset = 0
        self.read_error: str | None = None

    def poll(
        self,
        active_sessions: frozenset[str],
        now: float = 0.0,
        retired_sessions: frozenset[str] = frozenset(),
    ) -> None:
        if self.read_error is not None:
            return
        try:
            with self.path.open("rb") as stream:
                stream.seek(self.offset)
                data = stream.read(65536)
                self.offset += len(data)
        except OSError as error:
            self.read_error = str(error)
            return
        self.progress.observe(data, active_sessions, now, retired_sessions)

    def report(self, session: str) -> ProgressFileReport:
        try:
            unread = max(0, self.path.stat().st_size - self.offset)
        except OSError:
            unread = None
        return {
            **self.progress.report(session),
            "sidecar_path": str(self.path),
            "read_error": self.read_error,
            "consumed_bytes": self.offset,
            "unread_bytes": unread,
        }


def profile_log_path(run_path: Path, *, force: bool = False) -> tuple[str | None, bool]:
    """Resolve ISABELLE_PROOF_PROFILE_LOG, reserving a fresh run-local file for ``1``.

    Explicit nonempty values remain caller-owned paths.  The sentinel ``1``
    requests an exclusive file under this evidence run so timeout diagnostics
    can be inspected even if the guarded process is terminated.
    """
    setting = os.environ.get("ISABELLE_PROOF_PROFILE_LOG", "")
    if not setting and force:
        setting = "1"
    if not setting:
        return None, False
    if setting != "1":
        return setting, True
    for _attempt in range(32):
        path = run_path / f"isabelle-profile-{uuid4().hex}.log"
        try:
            with path.open("x", encoding="utf-8"):
                pass
        except FileExistsError:
            continue
        return str(path), True
    raise FileExistsError("could not reserve a fresh Isabelle profile log")
