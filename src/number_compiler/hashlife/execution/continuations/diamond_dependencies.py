"""Store-free diamond dependencies operations."""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Result,
    Task,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


def execute(self: DiamondRuntime, root: Task) -> Result:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import _Frame

    """One trampoline for all temporal, spatial, and observation requests."""
    frames: list[_Frame] = []
    task = self._canonical_task(root)
    result: Result = 0
    descending = True
    try:
        while True:
            self.ledger.bump(_execution_keys.SCHEDULER_TRANSITIONS)
            if descending:
                cached = self._probe_admitted(task)
                if cached is not None:
                    result = cached
                else:
                    program = self._program(task)
                    frames.append(_Frame(task, program))
                    peak = self.ledger.counters.get(
                        _execution_keys.SCHEDULER_WORKSPACE_PEAK, 0
                    )
                    if len(frames) > peak:
                        self.ledger.bump(
                            _execution_keys.SCHEDULER_WORKSPACE_PEAK,
                            len(frames) - peak,
                        )
                    try:
                        task = next(program)
                    except StopIteration as done:
                        frame = frames.pop()
                        result = cast(Result, done.value)
                        self._publish(frame.task, result)
                    else:
                        task = self._canonical_task(task)
                        continue
            if not frames:
                return result
            try:
                task = frames[-1].program.send(result)
            except StopIteration as done:
                frame = frames.pop()
                result = cast(Result, done.value)
                self._publish(frame.task, result)
                descending = False
            else:
                task = self._canonical_task(task)
                descending = True
    finally:
        for frame in frames:
            frame.program.close()
