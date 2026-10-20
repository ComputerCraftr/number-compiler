"""The source-image scheduler path does not import physical execution."""

from __future__ import annotations

import subprocess
import sys


def test_source_only_scheduler_rejects_physical_import_fanout() -> None:
    program = r"""
import importlib.abc
import sys

forbidden = {
    "number_compiler.hashlife.execution.tile_application_authority",
    "number_compiler.hashlife.execution.tile_causal_interfaces",
    "number_compiler.hashlife.execution.tile_clock_dispatch",
    "number_compiler.hashlife.execution.tile_execution_adapter",
    "number_compiler.hashlife.interfaces.diamond_quotient",
    "number_compiler.hashlife.tiles.tile_context",
    "number_compiler.hashlife.tiles.tile_results",
    "number_compiler.resources.causal_workspace",
    "number_compiler.resources.tile_dependency_leases",
    "number_compiler.sequences.collatz.physical_support",
}

class RejectPhysicalImports(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path=None, target=None):
        if fullname in forbidden:
            raise AssertionError("source-only scheduler imported " + fullname)
        return None

sys.meta_path.insert(0, RejectPhysicalImports())
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import ResourceLedger

scheduler = TileScheduler.source_only(ResourceLedger())
assert type(scheduler) is TileScheduler
assert not (forbidden & sys.modules.keys())
scheduler.dispose_source_images()
"""
    subprocess.run(
        [sys.executable, "-I", "-c", program],
        check=True,
        capture_output=True,
        text=True,
    )
