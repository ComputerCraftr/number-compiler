"""Check the optional C++20 kernels with compiler-specific diagnostics."""

import argparse
import subprocess
import sys
import sysconfig
import tempfile
from pathlib import Path

from devtools.runs import run_reported

_NATIVE = (
    Path("src/number_compiler/kernels/native_reverse"),
    Path("src/number_compiler/kernels/native_cf"),
)
_COMMON_WARNINGS = (
    "-Wall",
    "-Wextra",
    "-Wpedantic",
    "-Wcast-qual",
    "-Wconversion",
    "-Wdouble-promotion",
    "-Wfloat-equal",
    "-Wformat=2",
    "-Wimplicit-fallthrough",
    "-Wpointer-arith",
    "-Wsign-conversion",
    "-Wswitch-enum",
    "-Wundef",
    "-Wunused-but-set-parameter",
    "-Wunused-but-set-variable",
    "-Wunused-const-variable",
    "-Wunused-function",
    "-Wunused-local-typedefs",
    "-Wunused-macros",
    "-Wunused-parameter",
    "-Wunused-value",
    "-Wunused-variable",
    "-Wvla",
    "-Wwrite-strings",
)
_CLANG_WARNINGS = (
    "-Wcast-align",
    "-Wmissing-prototypes",
    "-Wnewline-eof",
    "-Wnull-dereference",
    "-Wshadow-all",
    "-Wunreachable-code",
    "-Wunreachable-code-break",
    "-Wunreachable-code-return",
    "-Wunused-lambda-capture",
    "-Wunused-private-field",
    "-Wunneeded-internal-declaration",
)
_GCC_WARNINGS = (
    "-Wcast-align=strict",
    "-Wduplicated-branches",
    "-Wduplicated-cond",
    "-Wformat-overflow=2",
    "-Wformat-truncation=2",
    "-Wlogical-op",
    "-Wmissing-declarations",
    "-Wshadow=local",
    "-Wstringop-overflow=4",
)


def _compile_options() -> list[str]:
    options = ["-std=c++20", "-fPIC", "-DNDEBUG", "-DPY_SSIZE_T_CLEAN"]
    python_headers = dict.fromkeys(
        sysconfig.get_path(layout) for layout in ("include", "platinclude")
    )
    for header in python_headers:
        options.extend(("-isystem", header))
    if sys.platform == "darwin":
        sdk = subprocess.check_output(("xcrun", "--show-sdk-path"), text=True).strip()
        options.extend(("-isysroot", sdk))
    return options


def _portable_warnings(compiler: str) -> list[str]:
    supported: list[str] = []
    macros = subprocess.check_output(
        (compiler, "-dM", "-E", "-x", "c++", "-"), input=b""
    ).splitlines()
    defined = {line.split()[1] for line in macros if line.startswith(b"#define ")}
    if b"__clang__" in defined:
        specific = _CLANG_WARNINGS
    elif b"__GNUC__" in defined:
        specific = _GCC_WARNINGS
    else:
        raise ValueError(f"unsupported native quality compiler: {compiler}")
    requested = (*_COMMON_WARNINGS, *specific)
    check = (compiler, "-Werror", "-x", "c++", "-fsyntax-only", "-")
    if (
        subprocess.run((*check, *requested), input=b"", capture_output=True).returncode
        == 0
    ):
        return list(requested)
    for warning in requested:
        probe = subprocess.run(
            (*check, warning),
            input="",
            capture_output=True,
            text=True,
            check=False,
        )
        if probe.returncode == 0:
            supported.append(warning)
        else:
            print(f"{compiler}: unavailable in C++ mode: {warning}", flush=True)
    return supported


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    compiler_options = parser.add_mutually_exclusive_group()
    compiler_options.add_argument("--llvm-bin", type=Path)
    compiler_options.add_argument(
        "--linux-compiler",
        help="Check a Linux C++ compiler with its supported warnings",
    )
    options = parser.parse_args()
    if options.linux_compiler and sys.platform != "linux":
        parser.error("--linux-compiler requires Linux")
    tools = options.llvm_bin or Path(".")
    clang = str(tools / "clang++")
    clang_format = str(tools / "clang-format")
    clang_tidy = str(tools / "clang-tidy")
    units = sorted(str(source) for root in _NATIVE for source in root.glob("[!.]*.cpp"))
    headers = sorted(
        str(source) for root in _NATIVE for source in root.glob("[!.]*.hpp")
    )
    if not units or not headers:
        parser.error("run from the repository root with the native sources present")
    compile_options = _compile_options()
    try:
        if options.linux_compiler:
            supported = _portable_warnings(options.linux_compiler)
            # GCC's overflow and range diagnostics need an optimizing compile.
            with tempfile.TemporaryDirectory() as objects:
                for unit in units:
                    subprocess.run(
                        (
                            options.linux_compiler,
                            *compile_options,
                            *supported,
                            "-Werror",
                            "-O2",
                            "-c",
                            unit,
                            "-o",
                            str(Path(objects) / (Path(unit).name + ".o")),
                        ),
                        check=True,
                    )
            return 0
        subprocess.run(
            (clang_format, "--dry-run", "--Werror", *units, *headers), check=True
        )
        clang_warnings = (
            (*_COMMON_WARNINGS, *_CLANG_WARNINGS)
            if sys.platform == "darwin"
            else _portable_warnings(clang)
        )
        subprocess.run(
            (
                clang,
                *compile_options,
                *clang_warnings,
                "-Werror",
                "-Werror=unknown-warning-option",
                "-fsyntax-only",
                *units,
            ),
            check=True,
        )
        subprocess.run((clang_tidy, "--verify-config"), check=True)
        subprocess.run(
            (clang_tidy, *units, "--", *compile_options),
            check=True,
        )
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Native kernel quality checks failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(run_reported(main))
