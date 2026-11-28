"""Source-bound Antihydra machine actions and demanded observations."""

from typing import TYPE_CHECKING

from number_compiler.api.lazy_exports import resolve_export as _resolve_export

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.runtime import (
        AntihydraArithmeticTerm as AntihydraArithmeticTerm,
    )
    from number_compiler.sequences.antihydra.runtime import (
        ArithmeticResult as ArithmeticResult,
    )
    from number_compiler.sequences.antihydra.runtime import Run as Run
    from number_compiler.sequences.antihydra.runtime import run as run

__all__ = ["AntihydraArithmeticTerm", "ArithmeticResult", "Run", "run"]
_EXPORT_MODULES = dict.fromkeys(__all__, "number_compiler.sequences.antihydra.runtime")


def __getattr__(name: str) -> object:
    return _resolve_export(name, _EXPORT_MODULES, globals())


def __dir__() -> list[str]:
    return sorted(set(globals()) | _EXPORT_MODULES.keys())
