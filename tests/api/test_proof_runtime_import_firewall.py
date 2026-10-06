"""Public family queries do not admit compatibility or proof executors."""

from __future__ import annotations

import json
import subprocess
import sys


def test_public_family_queries_leave_proof_and_legacy_executors_unloaded() -> None:
    program = r"""
import json
import sys
from number_compiler import NumberCompiler, PoweredCollatzTerm, ReverseAddPoweredTerm
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError

rejected = []
queries = (
    lambda: ReverseAddPoweredTerm(196, 2).digit(0),
    lambda: ReverseAddPoweredTerm(196, 2).width(),
    lambda: PoweredCollatzTerm(27, 2).digit(0),
    lambda: PoweredCollatzTerm(27, 2).width(),
    lambda: NumberCompiler().project_nth("collatz", 2, seed=27, radix=3).digit(0),
)
for query in queries:
    try:
        query()
    except UnsupportedInterfaceError as error:
        rejected.append(str(error))
forbidden = (
    "devtools.verification.block_composed",
    "devtools.verification.block_runtime",
    "number_compiler.sequences.collatz.physical_kernel",
    "number_compiler.hashlife.execution.diamond_reverse_kernel",
    "devtools.verification.collatz_c4_reference",
)
print(json.dumps({
    "loaded": [name for name in forbidden if name in sys.modules],
    "rejected": rejected,
}))
"""
    completed = subprocess.run(
        [sys.executable, "-c", program],
        check=True,
        capture_output=True,
        text=True,
    )
    result = json.loads(completed.stdout)
    assert result["loaded"] == []
    assert result["rejected"] == []


def test_composed_effect_requires_an_explicit_developer_import() -> None:
    program = r"""
import json
import sys
import number_compiler
before = "devtools.verification.block_runtime" in sys.modules
root_export = hasattr(number_compiler, "ComposedBlockEffect")
from devtools.verification.block_composed import ComposedBlockEffect
print(json.dumps((before, root_export, ComposedBlockEffect.__name__, "devtools.verification.block_runtime" in sys.modules)))
"""
    completed = subprocess.run(
        [sys.executable, "-c", program], check=True, capture_output=True, text=True
    )
    assert json.loads(completed.stdout) == [False, False, "ComposedBlockEffect", True]
