"""Track real Isabelle session build events inside a guarded build process."""

from __future__ import annotations

import math
import re

from devtools.checks.isabelle_proof_progress import ProofProgressFile
from devtools.checks.validation_policy import ISABELLE_SESSION_SECONDS

SESSION_STATUS = re.compile(
    r"^\s*(Running|Building|Finished|Failed|FAILED|Unfinished)\s+"
    r"([A-Za-z0-9_][A-Za-z0-9_.+-]*)(?:\s|\(|$)"
)
SESSION_NAME_FIRST_TERMINAL = re.compile(
    r"^\s*([A-Za-z0-9_][A-Za-z0-9_.+-]*)\s+"
    r"(FAILED|CANCELLED)(?:\s|\(|$)"
)
SESSION_DURATION = re.compile(r"\((\d+:\d{2}:\d{2}(?:\.\d+)?) elapsed time")
SESSION_NAME = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9_.+-]*$")
_UNFINISHED_LIST = re.compile(r"^\s*Unfinished session\(s\):\s*(.+)$")
_MAX_PARTIAL_LINE_BYTES = 64 * 1024


def parse_session_inventory(
    text: str, required_sessions: tuple[str, ...]
) -> tuple[str, ...]:
    """Parse Isabelle's authoritative topological `sessions -b` output."""
    names = tuple(
        line.strip()
        for line in text.splitlines()
        if SESSION_NAME.fullmatch(line.strip())
    )
    if not names or len(names) != len(set(names)):
        raise ValueError("Isabelle session inventory is empty or contains duplicates")
    missing = sorted(set(required_sessions) - set(names))
    if missing:
        raise ValueError(
            "native Isabelle inventory omitted requested sessions: "
            + ", ".join(missing)
        )
    return names


def session_build_summary(
    text: str, inventory: tuple[str, ...], *, succeeded: bool
) -> dict[str, object]:
    """Separate rebuilt, reused and unclassified heaps from native build logs."""
    started: set[str] = set()
    finished: set[str] = set()
    failed: set[str] = set()
    durations: dict[str, float] = {}
    for line in text.splitlines():
        unfinished_match = _UNFINISHED_LIST.match(line)
        if unfinished_match:
            failed.update(
                name.strip()
                for name in unfinished_match.group(1).split(",")
                if name.strip()
            )
            continue
        match = SESSION_STATUS.match(line)
        if match is None:
            continue
        status, name = match.groups()
        if status == "Finished" and name == "at" and name not in inventory:
            # Isabelle's build footer is a timestamp, not a rebuilt session.
            continue
        if status in {"Running", "Building"}:
            started.add(name)
        elif status == "Finished":
            finished.add(name)
            duration_match = SESSION_DURATION.search(line)
            if duration_match:
                hours, minutes, seconds = duration_match.group(1).split(":")
                durations[name] = int(hours) * 3600 + int(minutes) * 60 + float(seconds)
        else:
            failed.add(name)
    rebuilt = started | finished
    unknown = sorted(set(inventory) - rebuilt - failed)
    unmatched = sorted((started | finished | failed) - set(inventory))
    if succeeded and not failed:
        reused: list[str] | None = sorted(set(inventory) - rebuilt)
        inferred = "successful native build; inventory minus reported built sessions"
        not_attempted: list[str] = []
    else:
        reused = None
        inferred = None
        not_attempted = unknown
    return {
        "inventory_sessions": list(inventory),
        "inventory_count": len(inventory),
        "started_sessions": sorted(started),
        "rebuilt_sessions": sorted(rebuilt),
        "finished_sessions": sorted(finished),
        "failed_sessions": sorted(failed),
        "unmatched_native_session_statuses": unmatched,
        "reused_sessions": reused,
        "reused_inference": inferred,
        "not_attempted_or_unclassified_sessions": not_attempted,
        "finished_session_elapsed_seconds": durations or None,
        "over_budget_finished_sessions": sorted(
            name
            for name, seconds in durations.items()
            if seconds > ISABELLE_SESSION_SECONDS
        ),
    }


class IsabelleSessionWatchdog:
    """Enforce one non-resettable wall clock per inventory-admitted session.

    Only complete, anchored build status lines can start or finish timers.
    Isabelle's reused heaps have no start event and are never timed here.
    """

    def __init__(
        self,
        admitted_sessions: tuple[str, ...],
        limit_seconds: float,
        *,
        proof_progress: ProofProgressFile | None = None,
    ) -> None:
        if not math.isfinite(limit_seconds) or limit_seconds <= 0:
            raise ValueError("session limit must be positive and finite")
        if any(
            type(name) is not str or SESSION_NAME.fullmatch(name) is None
            for name in admitted_sessions
        ):
            raise ValueError("session inventory contains an invalid name")
        self.proof_progress = proof_progress
        self.admitted_sessions = frozenset(admitted_sessions)
        self.limit_seconds = limit_seconds
        self._partial = bytearray()
        self._discarding_long_line = False
        self._active: dict[str, float] = {}
        self._started: dict[str, float] = {}
        self._finished: set[str] = set()
        self._failed: set[str] = set()
        self._cancelled: set[str] = set()
        self.timed_out_session: str | None = None
        self.timed_out_elapsed_seconds: float | None = None

    def observe_output(self, data: bytes, now: float) -> None:
        """Consume pipe bytes while retaining incomplete lines between reads."""
        if not data or self.timed_out_session is not None:
            return
        if not math.isfinite(now):
            raise ValueError("watchdog time must be finite")
        self._poll_progress(now)
        self._expire(now)
        if self.timed_out_session is not None:
            return
        for byte in data:
            if self._discarding_long_line:
                if byte == 10:
                    self._discarding_long_line = False
                continue
            if byte == 10:
                self._consume_line(
                    bytes(self._partial).decode("utf-8", errors="replace"), now
                )
                self._partial.clear()
                if self.timed_out_session is not None:
                    return
                continue
            self._partial.append(byte)
            if len(self._partial) > _MAX_PARTIAL_LINE_BYTES:
                self._partial.clear()
                self._discarding_long_line = True

    def check(self, now: float) -> str | None:
        """Return a stable timeout reason once an active session exhausts its budget."""
        if not math.isfinite(now):
            raise ValueError("watchdog time must be finite")
        self._poll_progress(now)
        self._expire(now)
        if self.timed_out_session is None:
            return None
        elapsed = self.timed_out_elapsed_seconds
        assert elapsed is not None
        return (
            f"Isabelle session {self.timed_out_session} exceeded "
            f"{self.limit_seconds:g} seconds (elapsed {elapsed:.3f}s)"
        )

    def finish_output(self, now: float) -> None:
        """Consume a final unterminated line after the child closes its pipe."""
        if not math.isfinite(now):
            raise ValueError("watchdog time must be finite")
        self._poll_progress(now, final=True)
        self._expire(now)
        if self.timed_out_session is not None:
            self._partial.clear()
            self._discarding_long_line = False
            return
        if self._partial and not self._discarding_long_line:
            self._consume_line(
                bytes(self._partial).decode("utf-8", errors="replace"), now
            )
        self._partial.clear()
        self._discarding_long_line = False

    def report(self) -> dict[str, object]:
        """Return JSON-safe observations without implying reused heaps were built."""
        return {
            "admitted_session_count": len(self.admitted_sessions),
            "started_sessions": sorted(self._started),
            "finished_sessions": sorted(self._finished),
            "failed_sessions": sorted(self._failed),
            "cancelled_sessions": sorted(self._cancelled),
            "active_sessions": sorted(self._active),
            "timed_out_session": self.timed_out_session,
            "timed_out_elapsed_seconds": self.timed_out_elapsed_seconds,
            "limit_seconds": self.limit_seconds,
            "partial_line_bytes": len(self._partial),
        }

    def _poll_progress(self, now: float, *, final: bool = False) -> None:
        if self.timed_out_session is not None:
            # Keep the cutoff observation even if termination emits failures.
            return
        sessions = self._started if final else self._active
        if self.proof_progress is not None and sessions:
            self.proof_progress.poll(
                frozenset(sessions),
                now,
                frozenset(self._finished | self._failed | self._cancelled),
            )

    def _consume_line(self, line: str, now: float) -> None:
        terminal_match = SESSION_NAME_FIRST_TERMINAL.match(line)
        if terminal_match is not None:
            name, status = terminal_match.groups()
        else:
            match = SESSION_STATUS.match(line)
            if match is None:
                return
            status, name = match.groups()
        if name not in self.admitted_sessions:
            return
        if status in {"Running", "Building"}:
            # Duplicate lines and retries retain the first observed start.
            # A completed session cannot be restarted within the same build.
            if name not in self._finished and name not in self._active:
                started = self._started.setdefault(name, now)
                self._active[name] = started
                self._poll_progress(now)
                self._expire(now)
            return
        if status not in {"Finished", "Failed", "FAILED", "CANCELLED"} or (
            name not in self._active
        ):
            return
        self._poll_progress(now)
        started = self._active[name]
        elapsed = max(0.0, now - started)
        duration_match = SESSION_DURATION.search(line)
        if duration_match is not None:
            hours, minutes, seconds = duration_match.group(1).split(":")
            elapsed = max(
                elapsed, int(hours) * 3600 + int(minutes) * 60 + float(seconds)
            )
        if elapsed >= self.limit_seconds:
            self._record_timeout(name, elapsed)
            return
        del self._active[name]
        if status == "Finished":
            self._finished.add(name)
        elif status in {"Failed", "FAILED"}:
            self._failed.add(name)
        else:
            self._cancelled.add(name)

    def _expire(self, now: float) -> None:
        if self.timed_out_session is not None:
            return
        for name, started in self._active.items():
            elapsed = max(0.0, now - started)
            if elapsed >= self.limit_seconds:
                self._record_timeout(name, elapsed)
                return

    def _record_timeout(self, name: str, elapsed: float) -> None:
        self.timed_out_session = name
        self.timed_out_elapsed_seconds = elapsed
