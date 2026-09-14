import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

wheel = Path(
    "/tmp/python-quality-cleanup-wheel-2026-09-14/number_compiler-0.59.9-py3-none-any.whl"
)
cases = [
    (["196", "--nth", "16"], "897100798"),
    (["reverse-add", "--seed", "89", "--nth", "1"], "187"),
    (["collatz", "--seed", "27", "--nth", "10"], "214"),
    (["prime", "--nth", "100"], "547"),
    (["fermat", "--nth", "5"], "4294967297"),
    (["mersenne", "--nth", "131"], str((1 << 131) - 1)),
    (["antihydra", "--nth", "10"], "454"),
]
env = dict(os.environ)
env.pop("PYTHONPATH", None)
with tempfile.TemporaryDirectory(prefix="python-quality-installed-") as directory:
    root = Path(directory)
    subprocess.run(
        [sys.executable, "-m", "venv", str(root / "venv")],
        check=True,
        capture_output=True,
        env=env,
    )
    python = root / "venv/bin/python"
    subprocess.run(
        [str(python), "-m", "pip", "install", "--no-index", "--no-deps", str(wheel)],
        check=True,
        capture_output=True,
        env=env,
    )
    rows = []
    for args, expected in cases:
        for fmt in ("value", "json"):
            result = subprocess.run(
                [str(python), "-I", "-m", "number_compiler", *args, "--format", fmt],
                cwd=root,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            assert result.returncode == 0, (args, result)
            assert not result.stderr, (args, result.stderr)
            observed = (
                json.loads(result.stdout)["value"]
                if fmt == "json"
                else result.stdout.strip()
            )
            assert observed == expected, (args, observed, expected)
            rows.append({"args": args, "format": fmt, "value": observed})
    print(json.dumps({"cases": rows}, indent=2))
