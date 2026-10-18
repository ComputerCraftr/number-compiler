"""Track real Isabelle session build events inside a guarded build process."""

from __future__ import annotations

import math
import re

SESSION_STATUS = re.compile(
    r"^\s*(Running|Building|Finished|Failed|FAILED|Unfinished)\s+"
    r"([A-Za-z0-9_][A-Za-z0-9_.+-]*)(?:\s|\(|$)"
)
SESSION_DURATION = re.compile(r"\((\d+:\d{2}:\d{2}(?:\.\d+)?) elapsed time")
SESSION_NAME = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9_.+-]*$")
_MAX_PARTIAL_LINE_BYTES = 64 * 1024


class IsabelleSessionWatchdog:
    """Enforce one non-resettable wall clock per inventory-admitted session.

    Only complete, anchored build status lines can start or finish timers.
    Isabelle's reused heaps have no start event and are never timed here.
    """

    def __init__(
        self, admitted_sessions: tuple[str, ...], limit_seconds: float
    ) -> None:
        if not math.isfinite(limit_seconds) or limit_seconds <= 0:
            raise ValueError("session limit must be positive and finite")
        if any(
            type(name) is not str or SESSION_NAME.fullmatch(name) is None
            for name in admitted_sessions
        ):
            raise ValueError("session inventory contains an invalid name")
        self.admitted_sessions = frozenset(admitted_sessions)
        self.limit_seconds = limit_seconds
        self._partial = bytearray()
        self._discarding_long_line = False
        self._active: dict[str, float] = {}
        self._started: set[str] = set()
        self._finished: set[str] = set()
        self._failed: set[str] = set()
        self.timed_out_session: str | None = None
        self.timed_out_elapsed_seconds: float | None = None

    def observe_output(self, data: bytes, now: float) -> None:
        """Consume pipe bytes while retaining incomplete lines between reads."""
        if not data or self.timed_out_session is not None:
            return
        if not math.isfinite(now):
            raise ValueError("watchdog time must be finite")
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
            "active_sessions": sorted(self._active),
            "timed_out_session": self.timed_out_session,
            "timed_out_elapsed_seconds": self.timed_out_elapsed_seconds,
            "limit_seconds": self.limit_seconds,
            "partial_line_bytes": len(self._partial),
        }

    def _consume_line(self, line: str, now: float) -> None:
        match = SESSION_STATUS.match(line)
        if match is None:
            return
        status, name = match.groups()
        if name not in self.admitted_sessions:
            return
        if status in {"Running", "Building"}:
            # Never let duplicate or post-completion status lines reset time.
            if name not in self._started and name not in self._finished:
                self._started.add(name)
                self._active[name] = now
            return
        if status not in {"Finished", "Failed", "FAILED"} or name not in self._active:
            return
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
        else:
            self._failed.add(name)

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
