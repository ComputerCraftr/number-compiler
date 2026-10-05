"""Authoritative execution ceilings for repository validation.

Production query budgets and synthetic watchdog test inputs are independent.
"""

from dataclasses import dataclass

GIB = 1024**3
POLICY_VERSION = 1
PYTHON_TEST_SECONDS = 60
PYTHON_SUITE_SECONDS = 300
PYTHON_COMMAND_SECONDS = 60
PYTHON_MEMORY_BYTES = 4 * GIB
ISABELLE_SESSION_SECONDS = 60
ISABELLE_MEMORY_BYTES = 6 * GIB
ISABELLE_THREADS = 4
ISABELLE_PARALLEL_PROOFS = 1
ISABELLE_JOBS = 1
PYTEST_RUNNER_ENV = "NUMBER_COMPILER_GUARDED_PYTEST"
ISABELLE_JAVA_OPTIONS = "-Djava.awt.headless=true -Xms128m -Xmx1024m -Xss16m"
ISABELLE_ML_OPTIONS = "--minheap 128 --maxheap 4096"
ISABELLE_OPTIONS = (
    "threads=4",
    "parallel_proofs=1",
    "timeout=60",
    "timeout_scale=1",
)


@dataclass(frozen=True)
class ExecutionPolicy:
    """Wall-clock and aggregate process-tree ceilings for one invocation."""

    timeout_seconds: float
    memory_bytes: int


PYTHON_COMMAND = ExecutionPolicy(PYTHON_COMMAND_SECONDS, PYTHON_MEMORY_BYTES)
PYTHON_TEST = ExecutionPolicy(PYTHON_TEST_SECONDS, PYTHON_MEMORY_BYTES)
PYTHON_SUITE = ExecutionPolicy(PYTHON_SUITE_SECONDS, PYTHON_MEMORY_BYTES)


def isabelle_policy(session_count: int) -> ExecutionPolicy:
    """Allow orchestration overhead without extending native session timeouts."""
    if type(session_count) is not int or session_count < 0:
        raise ValueError("session_count must be a nonnegative integer")
    return ExecutionPolicy(
        ISABELLE_SESSION_SECONDS * (session_count + 1), ISABELLE_MEMORY_BYTES
    )
