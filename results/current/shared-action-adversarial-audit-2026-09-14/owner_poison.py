"""Check real CLI dependency on the rich prime action and higher 196 runtime."""

from contextlib import redirect_stderr, redirect_stdout
import io
import json
from unittest.mock import patch

from number_compiler.api import cli
from number_compiler.api.number_api import NumberCompiler
from number_compiler.hashlife.execution.continuations.higher_bimachine import HigherBimachineRuntime
from number_compiler.sequences.prime.successor_action import PrimeSuccessorActionArena


def run(owner, method, arguments):
    NumberCompiler().clear_shared_cache()
    output, errors = io.StringIO(), io.StringIO()
    trapped = False
    code = None
    with patch.object(owner, method, side_effect=AssertionError("audited owner invoked")):
        with redirect_stdout(output), redirect_stderr(errors):
            try:
                code = cli.main(arguments)
            except AssertionError as error:
                if str(error) != "audited owner invoked":
                    raise
                trapped = True
    return {
        "owner": owner.__name__, "method": method, "arguments": arguments,
        "poison_triggered": trapped, "exit_code": code,
        "stdout": output.getvalue(), "stderr": errors.getvalue(),
    }


if __name__ == "__main__":
    rows = [
        run(PrimeSuccessorActionArena, "__init__", ["prime", "--nth", "100"]),
        run(HigherBimachineRuntime, "point", ["196", "--nth", "4"]),
        run(HigherBimachineRuntime, "__init__", ["196", "--nth", "4"]),
        run(HigherBimachineRuntime, "point", ["196", "--nth", "8", "--no-value", "--info", "mirror"]),
    ]
    print(json.dumps({"scope": "bounded production owner poison checks", "rows": rows}))
